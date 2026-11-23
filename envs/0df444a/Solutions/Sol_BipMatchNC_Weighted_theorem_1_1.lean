-- Prove2me | solution 1 for BipMatchNC.Weighted.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:09:50.271717+00:00
-- url     : https://prove2.me/submissions/6ed096b3-0083-456d-b9d2-24aa5a6385c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_NC
import Definitions.Def_BipMatchNC_Weighted_Problems
import Theorems.Thm_BipMatchNC_Weighted_theorem_3_13

open BipMatchNC.Weighted

theorem solution : ∀ c : ℕ, ∃ k : ℕ,
    SearchInNC k (fun x : {x : WInstance // x.Bounded c} => x.1.enc)
      (fun x y => MaxWeightPMOutput x.1 y) := by
  intro c
  exact ⟨3, theorem_3_13 c⟩
