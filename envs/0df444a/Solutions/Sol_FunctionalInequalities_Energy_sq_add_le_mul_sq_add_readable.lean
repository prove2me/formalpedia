-- Prove2me | solution 1 for FunctionalInequalities.Energy.sq_add_le_mul_sq_add_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:37.812297+00:00
-- url     : https://prove2.me/submissions/a5874b44-debd-44c0-8b1a-0eea0672d3cc

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
universe u
section General
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- Young's inequality with a parameter, in the real line. -/
theorem FunctionalInequalities.Energy.real_sq_add_le {t a b : ℝ} (ht : 0 < t) :
    (a + b) ^ 2 ≤ (1 + t) * a ^ 2 + (1 + t⁻¹) * b ^ 2 := by
  have hX : 0 ≤ t * a ^ 2 + t⁻¹ * b ^ 2 - 2 * a * b := by
    have h2 : t * (t * a ^ 2 + t⁻¹ * b ^ 2 - 2 * a * b) = (t * a - b) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (t * a - b), ht]
  nlinarith [hX]
/-- Young's inequality with a parameter, in `ℝ≥0∞`, including the infinite values. -/
theorem solution {θ : ℝ≥0} (hθ : 0 < θ) (x y : ℝ≥0∞) :
    (x + y) ^ 2 ≤ (1 + (θ : ℝ≥0∞)) * x ^ 2 + (1 + (θ : ℝ≥0∞)⁻¹) * y ^ 2 := by
  have hθinv : ((θ : ℝ≥0∞))⁻¹ = ((θ⁻¹ : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_inv hθ.ne').symm
  rw [hθinv]
  rcases eq_or_ne x ⊤ with hx | hx
  · have h1 : (1 + (θ : ℝ≥0∞)) * x ^ 2 = ⊤ := by
      rw [hx, ENNReal.top_pow (by norm_num)]
      exact ENNReal.mul_top (by simp)
    rw [h1, top_add]
    exact le_top
  rcases eq_or_ne y ⊤ with hy | hy
  · have h1 : (1 + ((θ⁻¹ : ℝ≥0) : ℝ≥0∞)) * y ^ 2 = ⊤ := by
      rw [hy, ENNReal.top_pow (by norm_num)]
      exact ENNReal.mul_top (by simp)
    rw [h1, add_top]
    exact le_top
  obtain ⟨a, rfl⟩ : ∃ a : ℝ≥0, x = (a : ℝ≥0∞) := ⟨x.toNNReal, (ENNReal.coe_toNNReal hx).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℝ≥0, y = (b : ℝ≥0∞) := ⟨y.toNNReal, (ENNReal.coe_toNNReal hy).symm⟩
  have hnn : (a + b) ^ 2 ≤ (1 + θ) * a ^ 2 + (1 + θ⁻¹) * b ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact FunctionalInequalities.Energy.real_sq_add_le (by exact_mod_cast hθ)
  calc ((a : ℝ≥0∞) + (b : ℝ≥0∞)) ^ 2 = ((((a + b) ^ 2 : ℝ≥0)) : ℝ≥0∞) := by
        rw [ENNReal.coe_pow, ENNReal.coe_add]
    _ ≤ ((((1 + θ) * a ^ 2 + (1 + θ⁻¹) * b ^ 2 : ℝ≥0)) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hnn
    _ = (1 + (θ : ℝ≥0∞)) * (a : ℝ≥0∞) ^ 2 + (1 + ((θ⁻¹ : ℝ≥0) : ℝ≥0∞)) * (b : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_add,
          ENNReal.coe_one, ENNReal.coe_pow, ENNReal.coe_pow]
