-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:55:13.265975+00:00
-- url     : https://prove2.me/submissions/ce8da24a-c1e3-423a-bda9-6edd89faf05e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ν : Measure ℝ) [NullSingletonClass ν] :
    ∀ᵐ s ∂ν, 0 < s →
      riskProcess X x D s.toNNReal ω =
        x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω := by
  exact avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps
    X x D hD ω
    (avram_wave4_p2_all_original_levy_jump_times_countable X ω) ν
