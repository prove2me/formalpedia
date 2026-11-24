-- Prove2me | solution 1 for FairSelling.sum_restrictVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:15.493998+00:00
-- url     : https://prove2.me/submissions/ecf35ae8-ee45-4fcf-ab4e-33f6bc656e0e

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
theorem _root_.solution (R : Finset G) (w : G → ℝ) (s : Finset G) :
    ∑ g ∈ s, restrictVal R w g = ∑ g ∈ s ∩ R, w g := by
  classical
  unfold restrictVal
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
end FairSelling
