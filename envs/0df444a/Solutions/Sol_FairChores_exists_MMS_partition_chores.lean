-- Prove2me | solution 1 for FairChores.exists_MMS_partition_chores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:30:35.94508+00:00
-- url     : https://prove2.me/submissions/7040bccc-f435-4fa7-928b-f15807aa0c8c

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
import Theorems.Thm_FairChores_MMS_mem_chores

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
namespace FairChores
theorem _root_.solution (hn : 0 < n) (c p : T → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hp : ∀ t, 0 ≤ p t) :
    ∃ o : Outcome T n, o.Valid p ∧ ∀ j, cost c o j ≤ MMS n c p :=
  MMS_mem_chores hn c p hc hp
end FairChores
