-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_largejump_sum_L1_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:51:11.751402+00:00
-- url     : https://prove2.me/submissions/5064b519-3d12-4475-9d83-dfa855b29871

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18p_large_negative_mark_firstmoment_standing
import Theorems.Thm_AvramDividend_Classical_avram_ja18q_original_largejump_Campbell_lintegral_le
import Theorems.Thm_AvramDividend_Classical_avram_ja18r_original_largejump_ae_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original large-jump source integrability follows from Standing
first moment, intrinsic compensated-mark budget, and measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) P := by
  intro t
  have hMoment :
      (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) < ⊤ :=
    avram_ja18p_large_negative_mark_firstmoment_standing X hX
  have hBound :=
    avram_ja18q_original_largejump_Campbell_lintegral_le X hFinite t
  have hProduct :
      (t : ℝ≥0∞) *
        (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ne_of_lt hMoment)
  have hFiniteIntegral :
      HasFiniteIntegral
        (fun ω => avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) P := by
    change (∫⁻ ω, ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω‖ₑ ∂P) < ⊤
    exact lt_of_le_of_lt hBound (lt_top_iff_ne_top.mpr hProduct)
  exact ⟨avram_ja18r_original_largejump_ae_measurable X hFinite t,
    hFiniteIntegral⟩
