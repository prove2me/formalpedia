-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_uniform_count_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:03:26.638688+00:00
-- url     : https://prove2.me/submissions/1f1a25ca-61e7-491f-b9fd-b8a4ef028737

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under finite negative jump intensity, the physical full-cutoff marked
count has a second-moment bound independent of the cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let R : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    Integrable (fun ω => (N ω).toReal ^ 2) P ∧
      (∫ ω, (N ω).toReal ^ 2 ∂P) ≤ R ^ 2 + R := by
  intro B N R
  have hB : B ⊆ Iio (0 : ℝ) := by
    intro z hz
    have hdenom : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hfrac : (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
      one_div_pos.mpr hdenom
    have hzcut : -(1 / ((n : ℝ) + 1)) < 0 :=
      neg_lt_zero.mpr hfrac
    exact lt_of_le_of_lt hz hzcut
  have hMom :=
    avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
      X T n 0 T (by exact zero_le) le_rfl B measurableSet_Iic (Subset.rfl)
  have hTop : (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hFinite
  have hProduct :
      (T : ℝ≥0∞) * X.ν B ≤
        (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    gcongr
  have hRate :
      ((T : ℝ≥0∞) * X.ν B).toReal ≤ R := by
    exact ENNReal.toReal_mono hTop hProduct
  have hCutNonneg :
      0 ≤ ((T : ℝ≥0∞) * X.ν B).toReal := ENNReal.toReal_nonneg
  have hBound :
      ((T : ℝ≥0∞) * X.ν B).toReal ^ 2 +
        ((T : ℝ≥0∞) * X.ν B).toReal ≤ R ^ 2 + R := by
    gcongr
  refine ⟨hMom.1, ?_⟩
  exact le_trans hMom.2 hBound
