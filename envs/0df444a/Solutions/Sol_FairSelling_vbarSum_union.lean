-- Prove2me | solution 1 for FairSelling.vbarSum_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:49.946182+00:00
-- url     : https://prove2.me/submissions/aba0c2b7-8716-41e8-ab77-ad1dadccd988

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) {A B : Finset G} (h : Disjoint A B) :
    vbarSum w p (A ∪ B) = vbarSum w p A + vbarSum w p B := by
  simp only [vbarSum]; rw [Finset.sum_union h]
end FairSelling
