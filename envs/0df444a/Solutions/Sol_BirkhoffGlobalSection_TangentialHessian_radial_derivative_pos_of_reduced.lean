-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.radial_derivative_pos_of_reduced
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T17:40:49.701974+00:00
-- url     : https://prove2.me/submissions/30e56644-778c-4b75-9fcf-95c96e80e997

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

namespace BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian Filter Topology

noncomputable section

/-- `R² = (1-μ) - 2 zᵀ B z`, the squared radius of the momentum fiber of `K = 0`. -/
def radR2 (μ c Z u r : ℝ) : ℝ :=
  (1 - μ) - 2 * c * Z + 2 * μ * Z / r + (4 * Z ^ 2 + μ ^ 2) * Z - 4 * μ * Z * u

/-- `E = (1-μ) - 8Z³ + 4μZu + 4μZ(2Z² - u)/r³`. -/
def radE (μ Z u r : ℝ) : ℝ :=
  (1 - μ) - 8 * Z ^ 3 + 4 * μ * Z * u + 4 * μ * Z * (2 * Z ^ 2 - u) / r ^ 3

/-- `v = w + A(z) z = w - cen`. -/
def fibV1 (μ : ℝ) (s : Phase) : ℝ := s 2 - (2 * zNormSq s + μ) * s 1

def fibV2 (μ : ℝ) (s : Phase) : ℝ := s 3 + (2 * zNormSq s - μ) * s 0

theorem secondCollisionDistanceSq_eq (s : Phase) :
    secondCollisionDistanceSq s = 4 * zNormSq s ^ 2 - 4 * uCoord s + 1 := by
  unfold secondCollisionDistanceSq zNormSq uCoord; ring

theorem euler_identity (μ c r : ℝ) (hr : r ≠ 0) (s : Phase) :
    ∑ i, s i * kGradR μ c r s i =
      2 * (pP μ c s - μ * (zNormSq s / r)) + (1 - μ)
        + 4 * zNormSq s * (s 0 * s 3 - s 1 * s 2)
        + μ * zNormSq s * (16 * zNormSq s ^ 2 - 8 * uCoord s) / (2 * r ^ 3) := by
  simp only [Fin.sum_univ_four, kGradR]
  simp [dP, dZ, dD]
  unfold pP wNormSq zNormSq uCoord
  field_simp
  ring

theorem fiber_normSq (μ c r : ℝ) (hr : r ≠ 0) (s : Phase) :
    fibV1 μ s ^ 2 + fibV2 μ s ^ 2 =
      radR2 μ c (zNormSq s) (uCoord s) r + 2 * (pP μ c s - μ * (zNormSq s / r)) := by
  unfold fibV1 fibV2 radR2 pP wNormSq zNormSq uCoord
  field_simp
  ring

theorem cross_eq (μ : ℝ) (s : Phase) :
    s 0 * s 3 - s 1 * s 2 =
      (-2 * zNormSq s ^ 2 + μ * uCoord s) + (s 0 * fibV2 μ s - s 1 * fibV1 μ s) := by
  unfold fibV1 fibV2 zNormSq uCoord; ring

theorem lagrange (s : Phase) (v₁ v₂ : ℝ) :
    (s 0 * v₂ - s 1 * v₁) ^ 2 ≤ zNormSq s * (v₁ ^ 2 + v₂ ^ 2) := by
  unfold zNormSq; nlinarith [sq_nonneg (s 0 * v₁ + s 1 * v₂)]

theorem radE_eq (μ Z u r : ℝ) (hr : r ≠ 0) : radE μ Z u r = radEr3 μ Z u r / r ^ 3 := by
  unfold radE radEr3; field_simp

theorem radrR2_eq (μ c Z u r : ℝ) (hr : r ≠ 0) :
    radrR2 μ c Z u r = r * radR2 μ c Z u r := by
  unfold radrR2 radR2; field_simp; ring

theorem radF_eq (μ c Z u r : ℝ) (hr : r ≠ 0) :
    radE μ Z u r ^ 2 - 16 * Z ^ 3 * radR2 μ c Z u r = radFr6 μ c Z u r / r ^ 6 := by
  unfold radFr6
  rw [radE_eq μ Z u r hr, radrR2_eq μ c Z u r hr]
  field_simp

/-- `E > 0`, `E² > 16 Z³ R²` and `X² ≤ Z R²` give `E + 4 Z X > 0`. -/
theorem add_pos_of_sq_lt {E Z R2 X : ℝ} (hE : 0 < E)
    (hF : 0 < E ^ 2 - 16 * Z ^ 3 * R2) (hX : X ^ 2 ≤ Z * R2) : 0 < E + 4 * Z * X := by
  have h1 : (4 * Z * X) ^ 2 < E ^ 2 := by
    have : (4 * Z * X) ^ 2 = 16 * Z ^ 2 * X ^ 2 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 16 * Z ^ 2)]
  nlinarith [abs_lt_of_sq_lt_sq' h1 hE.le]

end

end BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.Sol

theorem solution (μ c r : ℝ) (s : Phase)
    (hr : 0 < r)
    (hK : pP μ c s - μ * (zNormSq s / r) = 0)
    (hpoly : 0 < radEr3 μ (zNormSq s) (uCoord s) r ∧
      0 < radFr6 μ c (zNormSq s) (uCoord s) r) :
    0 < ∑ i, s i * kGradR μ c r s i := by
  have hr0 := hr.ne'
  set Z := zNormSq s with hZdef
  set u := uCoord s with hudef
  have hfib := fiber_normSq μ c r hr0 s
  rw [hK, mul_zero, add_zero] at hfib
  obtain ⟨hE, hF⟩ := hpoly
  have hE' : 0 < radE μ Z u r := by rw [radE_eq μ Z u r hr0]; positivity
  have hF' : 0 < radE μ Z u r ^ 2 - 16 * Z ^ 3 * radR2 μ c Z u r := by
    rw [radF_eq μ c Z u r hr0]; positivity
  have hX : (s 0 * fibV2 μ s - s 1 * fibV1 μ s) ^ 2 ≤ Z * radR2 μ c Z u r := by
    rw [← hfib]; exact lagrange s _ _
  have key : ∑ i, s i * kGradR μ c r s i =
      radE μ Z u r + 4 * Z * (s 0 * fibV2 μ s - s 1 * fibV1 μ s) := by
    rw [euler_identity μ c r hr0 s, hK, cross_eq μ s]
    unfold radE
    field_simp
    ring
  rw [key]
  exact add_pos_of_sq_lt hE' hF' hX
