-- Prove2me | solution 1 for FairSelling.restrictVal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:25:15.31635+00:00
-- url     : https://prove2.me/submissions/f3ff84fa-bc31-4010-9bbe-2bcf94663986

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
theorem _root_.solution (R : Finset G) {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (g : G) :
    0 ≤ restrictVal R w g := by
  unfold restrictVal; split <;> [exact hw g; rfl]
end FairSelling
