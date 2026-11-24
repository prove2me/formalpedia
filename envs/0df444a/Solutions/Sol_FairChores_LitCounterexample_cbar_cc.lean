-- Prove2me | solution 1 for FairChores.LitCounterexample.cbar_cc
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:28:19.055167+00:00
-- url     : https://prove2.me/submissions/5890385a-8543-446c-8d9a-d9bbf5287175

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample


theorem solution : ∀ t, cbar (cc 0) pp t = 1 := by
  intro t; norm_num [cbar,cc,pp]
