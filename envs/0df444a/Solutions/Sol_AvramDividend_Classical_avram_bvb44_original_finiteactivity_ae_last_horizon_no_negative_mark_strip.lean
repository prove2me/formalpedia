-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb44_original_finiteactivity_ae_last_horizon_no_negative_mark_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:35:29.249958+00:00
-- url     : https://prove2.me/submissions/fb8e06bf-a10e-44d6-be5b-328c75b85bb9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb42_original_finite_negative_mark_times_terminal_margin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Genuine original spectrally negative finite-activity source paths have a
strict no-mark final strip at any fixed positive physical horizon, almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ≥0, 0 < t → t ≤ T →
          X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0 →
          (t : ℝ) ≤ (T : ℝ) - δ := by
  have hFiniteTimes :=
    avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
      X hBV hFinite T hT
  have hNoTerminal :=
    avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae X T hT
  filter_upwards [hFiniteTimes, hNoTerminal] with ω hFin hNo
  let S : Set ℝ≥0 := {t : ℝ≥0 |
    t ≤ T ∧ 0 < t ∧
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}
  have hSfinite : S.Finite := hFin
  have hCount : (Measure.count S) < ⊤ :=
    (Measure.count_apply_lt_top).2 hSfinite
  have hNoS : (⟨(T : ℝ), T.property⟩ : ℝ≥0) ∉ S := by
    change T ∉ S
    intro hmem
    exact hmem.2.2 hNo
  obtain ⟨δ,hδ,hGap⟩ :=
    avram_bvb42_original_finite_negative_mark_times_terminal_margin
      S hCount (T : ℝ) T.property hNoS
  refine ⟨δ,hδ,?_⟩
  intro t ht htT hJump
  apply hGap t
  · exact ⟨htT,ht,hJump⟩
  · exact_mod_cast htT
