-- Prove2me | solution 1 for DbarRegularity.maximalFunction_strongType
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:03:56.77482+00:00
-- url     : https://prove2.me/submissions/1ebcc614-f14f-4f84-ab1d-851c80e79a88

import Definitions.Def_DbarRegularity_Setting
import Theorems.Thm_DbarRegularity_maximalFunction_lowerSemicontinuous
import Theorems.Thm_DbarRegularity_maximalFunction_le_eLpNorm_top
import Theorems.Thm_DbarRegularity_maximalFunction_distribution_le
import Theorems.Thm_DbarRegularity_lintegral_rpow_le_of_distribution_le



namespace DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

/-- Strong type `(p, p)` of the Hardy–Littlewood maximal function for `1 < p ≤ ∞`. -/
theorem maximalFunction_strongType (d : ℕ) :
    ∀ p : ℝ≥0∞, 1 < p → ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      MemLp (maximalFunction f) p ∧
        eLpNorm (maximalFunction f) p volume ≤ A * eLpNorm f p volume := by
  intro p hp
  have hmeas : ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, Measurable (maximalFunction f) := fun f =>
    (maximalFunction_lowerSemicontinuous d f).measurable
  rcases eq_or_ne p ⊤ with rfl | hpt
  · refine ⟨1, fun f hf => ?_⟩
    have hle : eLpNorm (maximalFunction f) ⊤ volume ≤ eLpNorm f ⊤ volume := by
      rw [eLpNorm_exponent_top (f := maximalFunction f)]
      exact eLpNormEssSup_le_of_ae_enorm_bound
        (ae_of_all _ fun x => by rw [enorm_eq_self]; exact maximalFunction_le_eLpNorm_top d f x)
    refine ⟨⟨(hmeas f).aestronglyMeasurable, hle.trans_lt hf.2⟩, ?_⟩
    rw [ENNReal.coe_one, one_mul]
    exact hle
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  set r := p.toReal with hr
  have hr1 : 1 < r := by
    rw [hr, ← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono hpt hp
  have hr0 : 0 < r := zero_lt_one.trans hr1
  set K : ℝ≥0∞ := 2 ^ (r - 1) * (2 * (5 : ℝ≥0∞) ^ d) * ENNReal.ofReal (r / (r - 1)) with hK
  have hKt : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hKr : K ^ (1 / r) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hKt
  refine ⟨(K ^ (1 / r)).toNNReal, fun f hf => ?_⟩
  have hint : ∫⁻ x, maximalFunction f x ^ r ≤ K * ∫⁻ x, ‖f x‖ₑ ^ r :=
    lintegral_rpow_le_of_distribution_le volume (hmeas f).aemeasurable hf.1.enorm hr1
      (2 * (5 : ℝ≥0∞) ^ d) fun t ht => maximalFunction_distribution_le d f t ht
  have hle : eLpNorm (maximalFunction f) p volume ≤
      ((K ^ (1 / r)).toNNReal : ℝ≥0∞) * eLpNorm f p volume := by
    rw [ENNReal.coe_toNNReal hKr, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ← hr]
    simp only [enorm_eq_self]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    exact ENNReal.rpow_le_rpow hint (by positivity)
  exact ⟨⟨(hmeas f).aestronglyMeasurable,
    hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩, hle⟩

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

theorem solution (d : ℕ) :
    ∀ p : ℝ≥0∞, 1 < p → ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      MemLp (maximalFunction f) p ∧
        eLpNorm (maximalFunction f) p volume ≤ A * eLpNorm f p volume :=
  maximalFunction_strongType d
