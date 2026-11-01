-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_all_source_atomless_prejump_reserve_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:41:41.449242+00:00
-- url     : https://prove2.me/submissions/9f3d9c84-0de3-4bdc-a8e0-fb6d3d470d2e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ν : Measure ℝ) [NullSingletonClass ν] :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂ν, 0 < s →
      riskProcess X x D s.toNNReal ω =
        x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω := by
  refine Filter.Eventually.of_forall ?_
  intro ω
  exact avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps
    X x D hD ω (avram_wave4_p2_all_original_levy_jump_times_countable X ω) ν
