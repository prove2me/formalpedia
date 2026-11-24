-- Prove2me | solution 1 for FairChores.cbarSum_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:25:33.065634+00:00
-- url     : https://prove2.me/submissions/f11a033e-03c7-456a-88e3-ad4a341a772a

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (c p : T → ℝ) (t : T) : cbarSum c p ({t} : Finset T) = cbar c p t := by
  simp [cbarSum]
end FairChores
