import Mathlib

/-!
# Formal verification scaffold for
"測地線・法座標によるTEM誤差の幾何学的解明"

This file formalizes the algebraic core of equations (20)--(26) and
some exact identities around (16), (27)--(30).

IMPORTANT:
* The geometric/statistical identities (21)--(23) are represented as
  hypotheses in the theorem `eq20_to_eq24_1d`.
* The theorem then proves the algebraic consequence (24).
* Equation (26) is proved exactly by rational arithmetic.
* Monte-Carlo claims such as 95.05% coverage and KL=0.00020 are NOT
  treated as theorems here; those require a formalized probability model
  plus a certified numerical computation.

The next stage should replace the hypotheses for (21)--(23) by definitions
of the score, expected information, and the induced e-connection for the
normal model N(beta, beta^2).
-/

namespace TEMPaper

noncomputable section

open scoped BigOperators

/-! ## Equation (16): observed information -/

/-- The scalar specialization of equation (16). -/
def observedInformation (g H rN : ℝ) : ℝ := g - H * rN

/-- The paper's N(β, β²), β = 1 specialization of (16). -/
theorem eq16_normal_specialization (rho : ℝ) :
    observedInformation 3 (Real.sqrt ((2 : ℝ) / 3)) rho
      = 3 - rho * Real.sqrt ((2 : ℝ) / 3) := by
  simp [observedInformation]
  ring

/-! ## Equations (20)--(25): MLE bias reduction in one dimension -/

/-- Equation (20), specialized to p = 1.

The index sums each contain one term, so

  b = i⁻¹ ( i⁻¹ κ + (1/2) i⁻¹ ν ).
-/
def biasEq20 (i kappa nu : ℝ) : ℝ :=
  i⁻¹ * (i⁻¹ * kappa + (1 / 2 : ℝ) * i⁻¹ * nu)

/-- Equation (22), specialized to p = 1:
ν = -Γ - Γ - Γ - T = -3Γ - T.
-/
def nuEq22 (Gamma T : ℝ) : ℝ := -3 * Gamma - T

/-- Equation (23), specialized to p = 1: κ = Γ. -/
def kappaEq23 (Gamma : ℝ) : ℝ := Gamma

/-- M_a in equation (24), specialized to p = 1. -/
def M1 (i Gamma : ℝ) : ℝ := i⁻¹ * Gamma

/-- τ_a in equation (24), specialized to p = 1. -/
def tau1 (i T : ℝ) : ℝ := i⁻¹ * T

/-- Equation (24), specialized to p = 1. -/
def biasEq24 (i Gamma T : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * i⁻¹ * (M1 i Gamma + tau1 i T)

/-- Equation (25), specialized to p = 1, after setting Γ-trace M = 0. -/
def biasEq25 (i T : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * i⁻¹ * i⁻¹ * T

/--
Equations (20), (22), and (23) imply equation (24) in the one-dimensional
specialization.

This theorem does NOT assume the numerical values Γ = -10 and T = 14.
It proves the symbolic cancellation claimed in section 3.3.
-/
theorem eq20_to_eq24_1d
    (i Gamma T : ℝ)
    (hi : i ≠ 0) :
    biasEq20 i (kappaEq23 Gamma) (nuEq22 Gamma T)
      = biasEq24 i Gamma T := by
  simp [biasEq20, kappaEq23, nuEq22, biasEq24, M1, tau1]
  field_simp [hi]
  ring

/-- Equation (25) follows from equation (24) when M = 0.
For p = 1, M = i⁻¹ Γ, so it is enough to assume Γ = 0. -/
theorem eq24_to_eq25_1d
    (i Gamma T : ℝ)
    (hi : i ≠ 0)
    (hGamma : Gamma = 0) :
    biasEq24 i Gamma T = biasEq25 i T := by
  simp [biasEq24, biasEq25, M1, tau1, hGamma]
  field_simp [hi]

/-! ## Equation (26): exact arithmetic check -/

/-- The paper's numerical inputs for one observation at β = 1. -/
def fisher1 : ℝ := 3

def GammaNormal1 : ℝ := -10

def TNormal1 : ℝ := 14

/--
Equation (26), as an exact theorem over ℝ:

  -1/2 * (1/3) * ( (-10)/3 + 14/3 ) = -2/9.

Hence the reported theoretical value is established exactly, rather than
by floating-point approximation.
-/
theorem eq26_exact :
    biasEq24 fisher1 GammaNormal1 TNormal1 = -(2 : ℝ) / 9 := by
  norm_num [biasEq24, M1, tau1, fisher1, GammaNormal1, TNormal1]

/-- The same equation in the paper's "n · b(1)" notation. -/
theorem eq26_n_mul_bias :
    1 * biasEq24 fisher1 GammaNormal1 TNormal1 = -(2 : ℝ) / 9 := by
  simpa using eq26_exact

/-! ## A useful consistency check for the decomposition M + τ -/

theorem eq24_decomposes_as_squared_inverse
    (i Gamma T : ℝ) :
    biasEq24 i Gamma T =
      -(1 / 2 : ℝ) * (i⁻¹ * i⁻¹) * (Gamma + T) := by
  simp [biasEq24, M1, tau1]
  ring

/-! ## Equation (25) does not apply to the numerical coordinates used in (26)
unless one has first changed coordinates so that M = 0.

This is a formal consistency warning: with i = 3 and Γ = -10, M ≠ 0.
-/

theorem numerical_coordinate_has_nonzero_M :
    M1 fisher1 GammaNormal1 = -(10 : ℝ) / 3 := by
  norm_num [M1, fisher1, GammaNormal1]

theorem numerical_coordinate_not_in_eq25_gauge :
    M1 fisher1 GammaNormal1 ≠ 0 := by
  norm_num [M1, fisher1, GammaNormal1]

/-! ## Equations (27)--(30): exact algebraic definitions -/

/-- The sufficient direction V in equation (27), represented as a 2-vector.

NOTE (fix): the previous definition used `Fin.cases (S1 / betaHat)
(fun _ => 2 * S2 / betaHat)`. Whether `sufficientDirection ... 1` reduces to
the second branch *by `rfl`* depends on how the numeral `(1 : Fin 2)` unfolds
against `Fin.succ 0`, which is not guaranteed to be definitional in every
Mathlib version. `![·, ·]` (Matrix.cons / `Fin.cons` notation) is the
standard, robust way to write a concrete `Fin n → α` vector in Mathlib and
reduces via `simp [Matrix.cons_val_zero, Matrix.cons_val_one]` (or `decide`)
regardless of numeral representation, so it is used here instead. -/
def sufficientDirection (S1 S2 betaHat : ℝ) : Fin 2 → ℝ :=
  ![S1 / betaHat, 2 * S2 / betaHat]

/-- Component check for equation (27). -/
theorem eq27_components
    (S1 S2 betaHat : ℝ) :
    sufficientDirection S1 S2 betaHat 0 = S1 / betaHat ∧
    sufficientDirection S1 S2 betaHat 1 = 2 * S2 / betaHat := by
  constructor <;> simp [sufficientDirection]

/-- Equation (28), the scalar expression for the local canonical parameter. -/
def phiEq28 (S1 S2 betaHat beta : ℝ) : ℝ :=
  S1 / (betaHat * beta) - S2 / (betaHat * beta ^ 2)

/--
Equation (29), written as a direct definition.
The positivity assumptions needed for a fully analytic treatment of the
square-root/Wald statistic are intentionally kept outside this algebraic
scaffold.
-/
def qEq29 (phiHat phi j phiPrime : ℝ) : ℝ :=
  (phiHat - phi) * Real.sqrt j / phiPrime

/-- Equation (30), written as a direct definition. -/
def rStarEq30 (r q : ℝ) : ℝ :=
  r + (1 / r) * Real.log (q / r)

/-- A basic exact sanity check for (30): when q = r, r* = r. -/
theorem rStar_eq_r_when_q_eq_r
    (r : ℝ) (hr : r ≠ 0) :
    rStarEq30 r r = r := by
  simp [rStarEq30, hr]

/-! ## End-to-end algebraic chain for the reported numerical example -/

/--
Combining the one-dimensional reduction (20)--(24) with the numerical inputs
used in (26) gives the reported theoretical bias exactly.
-/
theorem eq20_to_eq26_chain :
    biasEq20 fisher1 (kappaEq23 GammaNormal1) (nuEq22 GammaNormal1 TNormal1)
      = -(2 : ℝ) / 9 := by
  calc
    biasEq20 fisher1 (kappaEq23 GammaNormal1) (nuEq22 GammaNormal1 TNormal1)
        = biasEq24 fisher1 GammaNormal1 TNormal1 := by
          exact eq20_to_eq24_1d fisher1 GammaNormal1 TNormal1 (by norm_num [fisher1])
    _ = -(2 : ℝ) / 9 := eq26_exact

/-! ## Cross-check against Part 1 (`AncillaryHolonomy`)

Part 1's example 6.1 (curved normal family, β = 1) computed
`g(H¹,H¹) = 2/3` for the Fisher metric `g(u,v) = u1v1+2u1v2+2u2v1+6u2v2`
and `H¹ = (-4/3, 1/3)`. This paper's equation (16) example uses the
*same* model and asserts the Efron-curvature norm is `√(2/3)`. This is a
non-trivial cross-check: the two independently-written papers must agree
on this number, since `√(2/3)` is exactly `√(g(H¹,H¹))` from Part 1. -/

private def gPart1 (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + 2 * u.1 * v.2 + 2 * u.2 * v.1 + 6 * u.2 * v.2

private def H1Part1 : ℝ × ℝ := (-4 / 3, 1 / 3)

/-- The `√(2/3)` appearing in `eq16_normal_specialization` is exactly
`√(g(H¹,H¹))` as computed independently in Part 1's example 6.1. -/
theorem part1_part2_curvature_norm_consistent :
    Real.sqrt (gPart1 H1Part1 H1Part1) = Real.sqrt ((2 : ℝ) / 3) := by
  norm_num [gPart1, H1Part1]

/-! ## What remains for a full paper verification -/

/-
A full verification still requires mathematical definitions, rather than
postulates, for the statistical/geometric objects in the paper. In
particular, the next stage should construct the normal model N(beta, beta^2),
its likelihood, score, expectations, and geometric tensors, and then prove
(21)--(23) from those definitions. The reported Monte-Carlo coverages and
KL divergences must be connected to a certified numerical experiment or to
exact probability bounds; they are deliberately not asserted as theorems
here.
-/

end

end TEMPaper
