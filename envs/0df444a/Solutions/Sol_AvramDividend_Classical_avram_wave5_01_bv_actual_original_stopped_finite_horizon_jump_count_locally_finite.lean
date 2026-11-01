-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_bv_actual_original_stopped_finite_horizon_jump_count_locally_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:27:12.931862+00:00
-- url     : https://prove2.me/submissions/c4d7f518-deff-4448-99ac-021fde82f237

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_count_locally_finite_all_borel_ae

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
      ((Measure.count.restrict {v : ℝ≥0 |
          0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
          (fun v : ℝ≥0 => (v,
            X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
          ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧ (u : ℝ≥0∞) ≤ τ ω} ×ˢ B) < ⊤ := by
  filter_upwards [avram_wave4_04a_bv_actual_intrinsic_count_locally_finite_all_borel_ae
    X hBV hFinite] with ω hω
  intro T B hB
  have hsub :
      ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧ (u : ℝ≥0∞) ≤ τ ω} ×ˢ B) ⊆
        (Ioc 0 T ×ˢ B) := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.1⟩, hp.2⟩
  exact lt_of_le_of_lt (measure_mono hsub) (hω T B hB)
