-- Prove2me | solution 1 for F6RotationSupport.interval_commonInc_supportUnion_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:16:16.852566+00:00
-- url     : https://prove2.me/submissions/48e88ded-4872-411b-889a-d70a40a222db

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_mem_supportUnion
import Theorems.Thm_F6RotationSupport_supports_disjoint_of_incomparable
import Theorems.Thm_F6RotationSupport_interval_commonInc_incomparable
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6RotationSupport.mem_supportUnion

set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]
namespace F6RotationSupport
theorem _root_.solution (supp : R → Finset M)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (alpha beta : R) :
    Disjoint (supportUnion supp (interval alpha beta))
      (supportUnion supp (commonInc alpha beta)) := by
  apply Finset.disjoint_left.mpr
  intro m hmA hmZ
  obtain ⟨a, ha, hma⟩ := mem_supportUnion.mp hmA
  obtain ⟨z, hz, hmz⟩ := mem_supportUnion.mp hmZ
  exact Finset.disjoint_left.mp
    (supports_disjoint_of_incomparable supp HSHARE
      (interval_commonInc_incomparable ha hz)) hma hmz
end F6RotationSupport
