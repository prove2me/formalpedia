-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_random_compact_reserve_negative_jump_joint_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:07:35.856579+00:00
-- url     : https://prove2.me/submissions/6ee5518c-4c1f-4c27-85c2-9f966bcb26cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Random compact reserve states retain finite original physical joint quadratic jump energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (U : Ω → ℝ) (hU : ∀ ω, U ω ∈ Icc δ K) :
    (∫⁻ ω, (∫⁻ z in Iio (0 : ℝ),
       ENNReal.ofReal ((w (U ω + z) - w (U ω)) ^ 2) ∂X.ν) ∂P) < ⊤ := by
  obtain ⟨M, hM0, hM⟩ :=
    avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
      w C hw_cont hw_neg hw_smooth δ K hδ hδK hK
  let b : ℝ → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (min (1 : ℝ) (z ^ 2))
  have hb : Measurable b :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.min (measurable_id.pow_const 2))
  have hEnergyFin :
      (∫⁻ z, ENNReal.ofReal M * b z ∂X.ν) < ⊤ := by
    rw [lintegral_const_mul (ENNReal.ofReal M) hb]
    exact ENNReal.mul_lt_top (by simp) X.ν_integrable
  have hBound (ω : Ω) :
      (∫⁻ z in Iio (0 : ℝ),
         ENNReal.ofReal ((w (U ω + z) - w (U ω)) ^ 2) ∂X.ν)
      ≤ (∫⁻ z, ENNReal.ofReal M * b z ∂X.ν) := by
    rw [← lintegral_indicator measurableSet_Iio]
    refine lintegral_mono ?_
    intro z
    by_cases hz : z < 0
    · have hzmem : z ∈ Iio (0 : ℝ) := hz
      rw [Set.indicator_of_mem hzmem]
      have hPoint := ENNReal.ofReal_le_ofReal (hM (U ω) (hU ω) z hz)
      simpa only [b, ENNReal.ofReal_mul hM0] using hPoint
    · have hznot : z ∉ Iio (0 : ℝ) := hz
      rw [Set.indicator_of_notMem hznot]
      exact bot_le
  calc
    (∫⁻ ω, (∫⁻ z in Iio (0 : ℝ),
       ENNReal.ofReal ((w (U ω + z) - w (U ω)) ^ 2) ∂X.ν) ∂P)
        ≤ (∫⁻ ω, (∫⁻ z, ENNReal.ofReal M * b z ∂X.ν) ∂P) :=
          lintegral_mono hBound
    _ = (∫⁻ z, ENNReal.ofReal M * b z ∂X.ν) := by
          simp [lintegral_const]
    _ < ⊤ := hEnergyFin
