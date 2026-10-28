-- Prove2me | solution 2 for AvramDividend.Classical.chat04_up_exit_time_pos_of_initial_safe_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:27:39.955583+00:00
-- url     : https://prove2.me/submissions/fffb40ae-6a31-4859-9234-e924bc1c1a7d

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (ω : Ω) (ε : ℝ≥0) (hε : 0 < ε)
    (hSafe : ∀ t : ℝ≥0, t < ε → X.X t ω ≤ b) :
    0 < twoSidedExitUpTime X b ω := by
  refine lt_of_lt_of_le (ENNReal.coe_pos.2 hε) ?_
  unfold twoSidedExitUpTime
  refine le_iInf₂ fun t ht => ENNReal.coe_le_coe.2 ?_
  by_contra h
  exact absurd (hSafe t (not_le.1 h)) (not_le.2 ht)
