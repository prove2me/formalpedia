-- Prove2me | solution 1 for F6RotationSupport.ci2_of_rotation_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:00:08.104862+00:00
-- url     : https://prove2.me/submissions/ff960b8a-e8c3-481b-b1bb-8190606ba63b

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_card_commonInc_le_two
import Theorems.Thm_F6RotationSupport_commonInc_chain

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
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    (HCAP3 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 3 → Q.card ≤ 2) :
    F6ConvexWindow.CI2 (V := R) := by
  intro alpha beta hab
  exact ⟨commonInc_chain supp H6 HMIN HSHARE HCAP2 hab,
    card_commonInc_le_two supp H6 HSHARE HCAP2 HCAP3 hab⟩
end F6RotationSupport
