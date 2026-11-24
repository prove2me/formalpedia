-- Prove2me | solution 1 for FairChores.LitCounterexample.oo_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:22:11.269365+00:00
-- url     : https://prove2.me/submissions/91eb65c1-5cff-479c-af6a-1e395e09f0c9

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample
namespace FairChores.LitCounterexample
theorem _root_.solution : oo.Valid pp := by
  refine ⟨by simp [oo], ?_, ?_, by simp [oo], by simp [oo]⟩
  · intro j k hjk
    simp [oo, hjk]
  · refine Finset.eq_univ_iff_forall.mpr fun t => ?_
    simp only [oo, Finset.empty_union, Finset.mem_biUnion]
    exact ⟨t, Finset.mem_univ _, by simp⟩
end FairChores.LitCounterexample
