-- Prove2me | solution 1 for F6RotationSupport.antichain_supports_pairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:07:06.623882+00:00
-- url     : https://prove2.me/submissions/94094ebc-c924-4ec3-8051-378953360ffd

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_supports_disjoint_of_incomparable
import Theorems.Thm_F6ConvexWindow_antichain_inc


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
    {A : Finset R} (hA : F6ConvexWindow.Antichain A) :
    (A : Set R).PairwiseDisjoint supp := by
  intro rho hrho sigma hsigma hne
  exact supports_disjoint_of_incomparable supp HSHARE
    (F6ConvexWindow.antichain_inc hA hrho hsigma hne)
end F6RotationSupport
