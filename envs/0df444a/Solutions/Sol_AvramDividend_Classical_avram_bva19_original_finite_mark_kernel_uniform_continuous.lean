-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva19_original_finite_mark_kernel_uniform_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:27:06.491163+00:00
-- url     : https://prove2.me/submissions/28f953c7-a320-4914-b329-01763600d7d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys108_BV_zero_reserve_contact_mark_null
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite source activity and Standing atomlessness give uniform kernel continuity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (s : Set ℝ) (hs : IsCompact s)
    (hsCap : s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    UniformContinuousOn
      (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) s := by
  have hνatom : ∀ a : ℝ, X.ν ({a} : Set ℝ) = 0 := by
    intro a
    have h := avram_bvb_phys108_BV_zero_reserve_contact_mark_null X hX hBV (-a)
    have hset : {z : ℝ | -a + z = 0} = ({a} : Set ℝ) := by
      ext z
      simp [add_eq_zero_iff_eq_neg]
    simpa only [hset] using h
  have hw_meas : Measurable w :=
    avram_p3_e_compensator_original_ruin_extension_value_measurable
      w hw_cont hw_neg
  exact avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
    C hFinite w hw_cont hw_neg hw_meas X.ν hActivity
    hνatom s hs hsCap
