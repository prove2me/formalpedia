-- Prove2me | solution 1 for FairSelling.cashVal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:23.874806+00:00
-- url     : https://prove2.me/submissions/fda9b430-e041-4612-95b8-e822c1a1872f

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_restrictVal_nonneg
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (R : Finset G) (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) :
    ∀ x, 0 ≤ cashVal R w x := by
  intro x
  cases x with
  | none => simp
  | some g => simpa using restrictVal_nonneg R hw g
end FairSelling
