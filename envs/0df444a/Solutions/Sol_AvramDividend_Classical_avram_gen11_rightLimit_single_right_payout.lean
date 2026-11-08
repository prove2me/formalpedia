-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen11_rightLimit_single_right_payout
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:29:23.048049+00:00
-- url     : https://prove2.me/submissions/257d464d-b818-418c-a172-7a24caee6b76

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- An adapted right payout at a path-dependent threshold is the right-limit atom. -/
theorem solution
    {Ω : Type*} (s : Ω → ℝ≥0) (A : Ω → ℝ) (ω : Ω) :
    rightLimit (fun t ω => if s ω < t then A ω else 0) (s ω) ω = A ω := by
  unfold rightLimit
  calc
    (⨅ u : Set.Ioi (s ω), if s ω < (u : ℝ≥0) then A ω else 0) =
        (⨅ _ : Set.Ioi (s ω), A ω) := by
          apply iInf_congr
          intro u
          exact if_pos u.property
    _ = A ω := by simp
