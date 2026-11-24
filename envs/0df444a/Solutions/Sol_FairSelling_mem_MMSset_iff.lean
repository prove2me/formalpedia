-- Prove2me | solution 1 for FairSelling.mem_MMSset_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:06.425807+00:00
-- url     : https://prove2.me/submissions/99d9746c-8152-433c-bf1b-503edc6cf5db

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Theorems.Thm_FairSelling_le_minUtil_iff

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v p : G → ℝ) (r : ℝ) :
    r ∈ MMSset n v p ↔ ∃ o : Outcome G n, o.Valid p ∧ r ≤ minUtil v o := by
  constructor
  · rintro ⟨o, hv, h⟩; exact ⟨o, hv, (le_minUtil_iff hn v o r).mpr h⟩
  · rintro ⟨o, hv, h⟩; exact ⟨o, hv, (le_minUtil_iff hn v o r).mp h⟩
end FairSelling
