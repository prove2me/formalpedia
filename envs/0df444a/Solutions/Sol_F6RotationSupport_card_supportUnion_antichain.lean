-- Prove2me | solution 1 for F6RotationSupport.card_supportUnion_antichain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:13:56.213784+00:00
-- url     : https://prove2.me/submissions/0f709516-abc7-422c-8c56-542e50f2bee2

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_antichain_supports_pairwiseDisjoint

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
    (supportUnion supp A).card = ∑ rho ∈ A, (supp rho).card := by
  exact Finset.card_biUnion (antichain_supports_pairwiseDisjoint supp HSHARE hA)
end F6RotationSupport
