-- Prove2me | solution 1 for FairSelling.restrictVal_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:13:31.533902+00:00
-- url     : https://prove2.me/submissions/b5e54e21-9f69-43cf-a991-ea4a7c9fb7bf

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (R : Finset G) (w : G → ℝ) {g : G} (hg : g ∈ R) :
    restrictVal R w g = w g := by simp [restrictVal, hg]
end FairSelling
