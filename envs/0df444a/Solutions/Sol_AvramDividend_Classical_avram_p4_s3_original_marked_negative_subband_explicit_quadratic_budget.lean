-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:26:32.677135+00:00
-- url     : https://prove2.me/submissions/dd9ad61b-02a9-495f-8abb-c41a096d65d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_marked_negative_borel_cell_dominated_by_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_square_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_ncard_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform explicit second-moment budget for actual original marked subband cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBsep : B ⊆ Iic (-(1 / ((n : ℝ) + 1)))) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let R : ℝ := ((T : ℝ≥0∞) *
      X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (N ω).toReal ^ 2) P ∧
      (∫ ω, (N ω).toReal ^ 2 ∂P) ≤ R ^ 2 + R := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let R : ℝ := ((T : ℝ≥0∞) *
    X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable (fun ω => (N ω).toReal ^ 2) P ∧
    (∫ ω, (N ω).toReal ^ 2 ∂P) ≤ R ^ 2 + R
  have hNm : Measurable N :=
    avram_p2_d_future_intrinsic_general_time_mark_measurable
      X (Ioc s t ×ˢ B) (measurableSet_Ioc.prod hB)
  have hKm : Measurable K :=
    avram_p4_f2_original_negative_band_ncard_measurable X T n
  have hK2 := avram_p4_s3_original_bounded_stop_negative_band_square_budget
    X T n (fun _ => T) (fun _ => le_rfl) hKm
  have hKr : Measurable (fun ω => (K ω : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hKm
  have hKL2 : MemLp (fun ω => (K ω : ℝ)) 2 P :=
    (memLp_two_iff_integrable_sq hKr.aestronglyMeasurable).2 hK2.1
  have hDom (ω : Ω) : (N ω).toReal ≤ (K ω : ℝ) :=
    avram_p4_s3_original_marked_negative_borel_cell_dominated_by_full_band
      X T n s t hst htT B hBsep ω
  have hNorm (ω : Ω) : ‖(N ω).toReal‖ ≤ ‖(K ω : ℝ)‖ := by
    have hn : 0 ≤ (N ω).toReal := ENNReal.toReal_nonneg
    have hk : 0 ≤ (K ω : ℝ) := Nat.cast_nonneg _
    simpa only [Real.norm_of_nonneg hn, Real.norm_of_nonneg hk] using hDom ω
  have hNL2 : MemLp (fun ω => (N ω).toReal) 2 P :=
    hKL2.mono ((ENNReal.measurable_toReal.comp hNm).aestronglyMeasurable)
      (Filter.Eventually.of_forall hNorm)
  have hN2 : Integrable (fun ω => (N ω).toReal ^ 2) P :=
    (memLp_two_iff_integrable_sq
      (ENNReal.measurable_toReal.comp hNm).aestronglyMeasurable).1 hNL2
  constructor
  · exact hN2
  · have hPoint (ω : Ω) :
        (N ω).toReal ^ 2 ≤ (K ω : ℝ) ^ 2 := by
      have hn : 0 ≤ (N ω).toReal := ENNReal.toReal_nonneg
      have hk : 0 ≤ (K ω : ℝ) := Nat.cast_nonneg _
      have hprod : 0 ≤ ((K ω : ℝ) - (N ω).toReal) *
          ((K ω : ℝ) + (N ω).toReal) :=
        mul_nonneg (sub_nonneg.mpr (hDom ω)) (add_nonneg hk hn)
      nlinarith
    have hI := integral_mono_ae hN2 hK2.1
      (Filter.Eventually.of_forall hPoint)
    exact hI.trans hK2.2
