-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_uniform_nu_square_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:11:05.43998+00:00
-- url     : https://prove2.me/submissions/ba016da2-6dbe-401e-b119-f007762e7055

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform finite original negative-mark quadratic energy on compact positive reserve states. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ S : ℝ≥0∞, S < ⊤ ∧
      ∀ u ∈ Icc δ K,
        (∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) ≤ S := by
  obtain ⟨M, hM0, hM⟩ :=
    avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
      w C hw_cont hw_neg hw_smooth δ K hδ hδK hK
  let b : ℝ → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (min (1 : ℝ) (z ^ 2))
  have hb : Measurable b :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.min (measurable_id.pow_const 2))
  let S : ℝ≥0∞ := ENNReal.ofReal M * (∫⁻ z, b z ∂X.ν)
  have hSfin : S < ⊤ :=
    ENNReal.mul_lt_top (by simp) X.ν_integrable
  refine ⟨S, hSfin, ?_⟩
  intro u hu
  have hPoint (z : ℝ) :
      (Iio (0 : ℝ)).indicator
        (fun z => ENNReal.ofReal ((w (u + z) - w u) ^ 2)) z
      ≤ ENNReal.ofReal M * b z := by
    by_cases hz : z < 0
    · have hzmem : z ∈ Iio (0 : ℝ) := hz
      rw [Set.indicator_of_mem hzmem]
      have hh := ENNReal.ofReal_le_ofReal (hM u hu z hz)
      simpa only [b, ENNReal.ofReal_mul hM0] using hh
    · have hznot : z ∉ Iio (0 : ℝ) := hz
      rw [Set.indicator_of_notMem hznot]
      exact bot_le
  calc
    (∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν)
        = ∫⁻ z, (Iio (0 : ℝ)).indicator
            (fun t => ENNReal.ofReal ((w (u + t) - w u) ^ 2)) z ∂X.ν :=
          (lintegral_indicator measurableSet_Iio _).symm
    _ ≤ ∫⁻ z, ENNReal.ofReal M * b z ∂X.ν :=
          lintegral_mono hPoint
    _ = S := by
      rw [lintegral_const_mul (ENNReal.ofReal M) hb]
