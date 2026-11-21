-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovestrip_true_generator_overshoot_integral_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:42:30.579697+00:00
-- url     : https://prove2.me/submissions/014a3b5e-897c-4ce7-bf48-083a06070cef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_truncated_negative_mark_overshoot_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (V : ℝ → ℝ)
    (hV : ∀ t : ℝ, V t =
      if t ≤ C.toReal then w t
      else w C.toReal + (t - C.toReal))
    (y : ℝ) (hy : C.toReal < y)
    (hGen : X.GeneratorIntegrable V y)
    (hOver : Integrable (fun z : ℝ => max 0 (-(y + z)))
      (X.ν.restrict (Iio (0 : ℝ)))) :
    X.generator V y ≤ X.c +
      (∫ z in Iio (0 : ℝ), max 0 (-(y + z)) ∂X.ν) := by
  have hv : V = (fun t : ℝ =>
      if t ≤ C.toReal then w t
      else w C.toReal + (t - C.toReal)) := funext hV
  subst V
  have hAE :
      (fun z : ℝ =>
        SpectrallyNegativeLevy.generatorIntegrand
          (fun t : ℝ =>
            if t ≤ C.toReal then w t
            else w C.toReal + (t - C.toReal)) y z)
      ≤ᵐ[X.ν.restrict (Iio (0 : ℝ))]
      (fun z : ℝ => max 0 (-(y + z))) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    have hmark :=
      avram_mix_inf20_original_finitecap_abovebarrier_truncated_negative_mark_overshoot_bound
        C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy hz
    have hGen :
        SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
          y z =
          (if y + z ≤ C.toReal then w (y + z) else
            w C.toReal + (y + z - C.toReal)) -
          (if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal)) -
          deriv (fun t => if t ≤ C.toReal then w t else
            w C.toReal + (t - C.toReal)) y *
            (if -1 < z then z else 0) := by
      unfold SpectrallyNegativeLevy.generatorIntegrand
      by_cases hsmall : -1 < z
      · have hz1 : z < 1 := lt_trans hz (by norm_num)
        simp [Set.indicator, Set.mem_Ioo, hsmall, hz1]
      · simp [Set.indicator, Set.mem_Ioo, hsmall]
    rw [hGen]
    exact hmark
  have hI :=
    integral_mono_ae hGen hOver hAE
  have hEq :=
    avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
      X w C.toReal y hy
  dsimp only at hEq
  linarith
