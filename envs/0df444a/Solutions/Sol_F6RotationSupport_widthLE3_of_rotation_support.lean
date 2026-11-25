-- Prove2me | solution 1 for F6RotationSupport.widthLE3_of_rotation_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:32:11.877884+00:00
-- url     : https://prove2.me/submissions/f86df25c-9892-4132-9566-b86552904cf9

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_two_mul_card_antichain_le_supportUnion

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
      rho ≤ sigma ∨ sigma ≤ rho) :
    F6ConvexWindow.WidthLE (V := R) 3 := by
  intro A hA
  have hcount := two_mul_card_antichain_le_supportUnion supp HMIN HSHARE hA
  have hmen := (supportUnion supp A).card_le_univ
  omega
end F6RotationSupport
