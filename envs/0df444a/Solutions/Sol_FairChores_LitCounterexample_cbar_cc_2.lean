-- Prove2me | solution 2 for FairChores.LitCounterexample.cbar_cc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:53:27.571778+00:00
-- url     : https://prove2.me/submissions/51cabdc4-6211-44e0-b9f9-52cccfabda1e

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
theorem _root_.solution : ∀ t, cbar (cc 0) pp t = 1 := by
  intro t; simp [cbar, cc, pp]
end FairChores.LitCounterexample
