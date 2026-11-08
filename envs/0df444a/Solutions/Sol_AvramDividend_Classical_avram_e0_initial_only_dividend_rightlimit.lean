-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_only_dividend_rightlimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:01:42.28651+00:00
-- url     : https://prove2.me/submissions/635ac26c-d0cb-4451-9525-919165149f48

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The initial-only cumulative dividend is constant strictly after any nonnegative time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (K : Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    rightLimit (fun s ω => if s = 0 then 0 else K ω) t ω = K ω := by
  unfold rightLimit
  calc
    (⨅ u : Set.Ioi t, if (u : ℝ≥0) = 0 then (0 : ℝ) else K ω) =
        (⨅ _ : Set.Ioi t, K ω) := by
          apply iInf_congr
          intro u
          have hpos : (0 : ℝ≥0) < u :=
            lt_of_le_of_lt (show (0 : ℝ≥0) ≤ t from zero_le) u.property
          exact if_neg (ne_of_gt hpos)
    _ = K ω := by simp
