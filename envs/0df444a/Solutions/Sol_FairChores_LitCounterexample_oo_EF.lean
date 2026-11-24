-- Prove2me | solution 1 for FairChores.LitCounterexample.oo_EF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:40.964645+00:00
-- url     : https://prove2.me/submissions/d4736d5f-2367-4231-bf88-10d43d9ff3c1

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
import Theorems.Thm_FairChores_LitCounterexample_cbarSum_single
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample
namespace FairChores.LitCounterexample
theorem _root_.solution : EF cc pp oo := by
  intro i j
  simp [oo, cbarSum_single]
end FairChores.LitCounterexample
