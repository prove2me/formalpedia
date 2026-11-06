-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_negative_band_compact_source_parameter_joint_L2_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:27:26.235593+00:00
-- url     : https://prove2.me/submissions/e0bfaf0f-10bd-4d7c-8323-b6889a744747

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative-band squared coefficient has finite energy for every compact-valued source parameter. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    {S : Type*} [mS : MeasurableSpace S]
    (μ : Measure S) (hμ : μ univ < ⊤)
    (U V : S → ℝ)
    (hU : ∀ s, U s ∈ Icc δ K)
    (hV : ∀ s, V s ∈ Icc δ K) :
    (∫⁻ s, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U s + z) - w (U s)) -
          (w (V s + z) - w (V s))) ^ 2) ∂X.ν) ∂μ) < ⊤ := by
  obtain ⟨Q, hQ0, hQ⟩ :=
    avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
      w C hw_cont hw_neg hw_smooth δ K hδ hδK hK
  let b : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min (1 : ℝ) (z ^ 2))
  have hb : Measurable b :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.min (measurable_id.pow_const 2))
  let E : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal Q * b z ∂X.ν
  have hEnergyFin : E < ⊤ := by
    dsimp [E]
    rw [lintegral_const_mul (ENNReal.ofReal Q) hb]
    exact ENNReal.mul_lt_top (by simp) X.ν_integrable
  have hBound (s : S) :
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U s + z) - w (U s)) -
            (w (V s + z) - w (V s))) ^ 2) ∂X.ν) ≤ E := by
    change (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U s + z) - w (U s)) -
          (w (V s + z) - w (V s))) ^ 2) ∂X.ν)
      ≤ (∫⁻ z, ENNReal.ofReal Q * b z ∂X.ν)
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_mono ?_
    intro z
    by_cases hz : z ∈ Ioo (-ε) (0 : ℝ)
    · rw [Set.indicator_of_mem hz]
      have hPoint := ENNReal.ofReal_le_ofReal
        (hQ (U s) (hU s) (V s) (hV s) z hz.2)
      simpa only [b, ENNReal.ofReal_mul hQ0] using hPoint
    · rw [Set.indicator_of_notMem hz]
      exact bot_le
  calc
    (∫⁻ s, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U s + z) - w (U s)) -
          (w (V s + z) - w (V s))) ^ 2) ∂X.ν) ∂μ)
      ≤ ∫⁻ _s : S, E ∂μ := lintegral_mono hBound
    _ = E * μ univ := by simp [lintegral_const, mul_comm]
    _ < ⊤ := ENNReal.mul_lt_top hEnergyFin hμ
