-- Prove2me | solution 2 for AvramDividend.Classical.chat04_up_exit_time_zero_of_positive_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:33:19.779862+00:00
-- url     : https://prove2.me/submissions/80f188ee-744f-4508-8eda-525750f4c461

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hNear : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitUpTime X 0 ω = 0 := by
  unfold twoSidedExitUpTime
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (zero_le (a := _))
  obtain ⟨t, htε, ht⟩ := hNear ε hε
  rw [zero_add]
  exact (iInf₂_le t ht).trans (by exact_mod_cast htε.le)
