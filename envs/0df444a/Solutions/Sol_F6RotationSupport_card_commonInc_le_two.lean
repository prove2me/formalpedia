-- Prove2me | solution 1 for F6RotationSupport.card_commonInc_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:50:48.796815+00:00
-- url     : https://prove2.me/submissions/2648d096-6fae-484f-be54-a7db56047f84

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_commonInc_orderConvex
import Theorems.Thm_F6RotationSupport_card_commonInc_supportUnion_le_three

set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]
namespace F6RotationSupport
theorem _root_.solution (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    (HCAP3 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 3 → Q.card ≤ 2)
    {alpha beta : R} (hab : alpha < beta) :
    (commonInc alpha beta).card ≤ 2 := by
  exact HCAP3 (commonInc alpha beta) (commonInc_orderConvex alpha beta)
    (card_commonInc_supportUnion_le_three supp H6 HSHARE HCAP2 hab)
end F6RotationSupport
