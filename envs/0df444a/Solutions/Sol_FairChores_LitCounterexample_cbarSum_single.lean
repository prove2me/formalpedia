-- Prove2me | solution 1 for FairChores.LitCounterexample.cbarSum_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:59.225912+00:00
-- url     : https://prove2.me/submissions/a5d625e6-5a4e-455d-a7dd-8046bd2ead42

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
theorem _root_.solution (i j : Fin 2) : cbarSum (cc i) pp {j} = 1 := by
  simp [cbarSum, cbar, cc, pp]
end FairChores.LitCounterexample
