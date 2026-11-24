-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.outKeepAll_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:32:19.159955+00:00
-- url     : https://prove2.me/submissions/4145687b-8cf0-42e8-abc1-76921ad97d89

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleFour
theorem _root_.solution : (outKeepAll N).Valid (price N) := by
  refine ⟨fun j => by simp [outKeepAll], fun j k hjk => by simp [outKeepAll, hjk],
    fun j => by simp [outKeepAll], by simp [outKeepAll]⟩
end FairSelling.EqualProceedsExampleFour
