-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_original_finite_activity_smallband_limit_square_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:50:03.039083+00:00
-- url     : https://prove2.me/submissions/1b69f64d-7262-40c2-8070-005b2c8c2fa1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18e_original_smallband_locally_uniform_cadlag_limit
import Theorems.Thm_AvramDividend_Classical_avram_anoise30_original_smallband_compensator_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_finite_activity_smallband_uniform_L2_count_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ja19_aesquare_dominated_limit_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      (∀ t : ℝ≥0, Integrable (fun ω => (Jsmall t ω) ^ 2) P) := by
  obtain ⟨Jsmall, hlimit, _, _⟩ :=
    avram_ja18e_original_smallband_locally_uniform_cadlag_limit X hX hFinite
  refine ⟨Jsmall, hlimit, ?_⟩
  intro t
  obtain ⟨B, hB, hbound⟩ :=
    avram_ja19_original_finite_activity_smallband_uniform_L2_count_envelope
      X hFinite t
  apply avram_ja19_aesquare_dominated_limit_integrable
    (fun k ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
    (Jsmall t) B
  · exact fun k => avram_anoise30_original_smallband_compensator_integrable
      X hFinite k t
  · filter_upwards [hlimit] with ω hω
    exact hω t
  · exact hB
  · filter_upwards [hbound] with ω hω
    intro k
    exact hω k t le_rfl
