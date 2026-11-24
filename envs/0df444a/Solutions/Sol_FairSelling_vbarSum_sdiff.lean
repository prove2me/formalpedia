-- Prove2me | solution 1 for FairSelling.vbarSum_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:46.273125+00:00
-- url     : https://prove2.me/submissions/e647cd5d-ee94-4ffa-b86e-7bfd7446638b

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) {X Y : Finset G} (h : Y ⊆ X) :
    vbarSum w p (X \ Y) = vbarSum w p X - vbarSum w p Y := by
  simp only [vbarSum]; rw [Finset.sum_sdiff_eq_sub h]
end FairSelling
