-- Prove2me | solution 1 for Eden.commonIndexCandidates_isLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:31.861202+00:00
-- url     : https://prove2.me/submissions/5ae2acb4-2b33-4769-bff9-d84b9132ed6f

import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_CommonIndex
import Theorems.Thm_Eden_supremumExponentSum_five
import Theorems.Thm_Eden_supremumExponentSum_nonneg


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    IsLeast (commonIndexCandidates c) 4 := by
  constructor
  · change 4 ≤ 4 ∧ supremumExponentSum c 5 < 0
    rw [supremumExponentSum_five hc]
    constructor <;> linarith
  · intro k hk
    by_contra h
    have hk₄ : k + 1 ≤ 4 := by omega
    exact (not_lt_of_ge (supremumExponentSum_nonneg hc hk₄)) hk.2
end Eden
