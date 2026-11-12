-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja19_original_finite_activity_zero_jump_gaussian_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:10:32.382961+00:00
-- url     : https://prove2.me/submissions/71364e3a-a3ed-4054-93b5-1d7f892ec4d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_finite_activity_smallband_limit_square_L1
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_zero_nu_process_from_finite_jump_source

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
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (t : ℝ≥0) :
    ∃ (Y : SpectrallyNegativeLevy P 𝓕) (J : Ω → ℝ),
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      Integrable (fun ω => (J ω) ^ 2) P ∧
      (∀ᵐ ω ∂P,
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
          (Y.X t ω - (t : ℝ) * Y.c) + J ω) := by
  obtain ⟨Jsmall, hSource, hSq⟩ :=
    avram_ja19_original_finite_activity_smallband_limit_square_L1 X hX hFinite
  obtain ⟨Y, hν, hσ, hId⟩ :=
    avram_ja19_original_zero_nu_process_from_finite_jump_source
      X hX hFinite Jsmall hSource
  refine ⟨Y, Jsmall t, hν, hσ, hSq t, ?_⟩
  filter_upwards [hId] with ω hω
  exact hω t
