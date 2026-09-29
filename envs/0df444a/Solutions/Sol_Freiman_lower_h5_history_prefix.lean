-- Prove2me | solution 1 for Freiman.lower_h5_history_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T04:16:10.089408+00:00
-- url     : https://prove2.me/submissions/f1688b9e-deee-4753-b0ed-ba09ec151e89

import Definitions.Def_Freiman_lowerSelection

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n m : ℕ)
    (hh : lowerHistory t h n) (hm : m ≤ n) : lowerHistory t h m := by
  unfold lowerHistory at hh ⊢
  refine ⟨hh.1, ?_, ?_⟩
  · intro j hj
    exact hh.2.1 j (le_trans hj hm)
  · intro j hj
    exact hh.2.2 j (lt_of_lt_of_le hj hm)
