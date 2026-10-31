-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_drained_zero_barrier_admissible_any_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:41:30.567988+00:00
-- url     : https://prove2.me/submissions/501c6bf5-9dfb-4d00-8f4b-fbac09df133c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_admissible_infinite_cap
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_reserve_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Strict reserve negativity at every positive time yields any cap bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) :
    IsAdmissibleLe X x C
      (fun t ω => barrierStrategy X x 0 t ω + (t : ℝ)) := by
  have hinf := drained_zero_barrier_admissible_infinite_cap X x hx
  rcases hinf with ⟨hD, _⟩
  refine ⟨hD, ?_⟩
  intro ω t ht
  have hneg : riskProcess X x
      (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω < 0 :=
    barrierStrategy_plus_linear_drain_reserve_negative X x hx ω t ht
  rw [ENNReal.ofReal_eq_zero.mpr (le_of_lt hneg)]
  exact bot_le
