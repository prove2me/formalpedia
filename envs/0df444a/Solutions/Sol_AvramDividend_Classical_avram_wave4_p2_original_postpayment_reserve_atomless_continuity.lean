-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_atomless_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:08:10.877202+00:00
-- url     : https://prove2.me/submissions/bca07b61-5148-4866-8f1e-73ce8c87291a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_jump_times_countable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ν : Measure ℝ≥0) [NullSingletonClass ν] :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂ν, 0 < t →
      x + X.X t ω - rightLimit D t ω =
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t := by
  refine Filter.Eventually.of_forall ?_
  intro ω
  apply ae_iff.mpr
  have hnull : ν {t : ℝ≥0 | 0 < t ∧
      x + X.X t ω - rightLimit D t ω ≠
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t} = 0 :=
    (avram_wave4_p2_original_postpayment_reserve_jump_times_countable
      X x D hD ω).measure_zero ν
  simpa only [_root_.not_imp] using hnull
