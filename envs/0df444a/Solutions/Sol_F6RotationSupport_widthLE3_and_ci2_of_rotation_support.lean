-- Prove2me | solution 1 for F6RotationSupport.widthLE3_and_ci2_of_rotation_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:04:54.773328+00:00
-- url     : https://prove2.me/submissions/83fbc37f-33e5-4aa5-ad2e-031f18079931

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_widthLE3_of_rotation_support
import Theorems.Thm_F6RotationSupport_ci2_of_rotation_support

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
    F6ConvexWindow.WidthLE (V := R) 3 ∧ F6ConvexWindow.CI2 (V := R) :=
  ⟨widthLE3_of_rotation_support supp H6 HMIN HSHARE,
    ci2_of_rotation_support supp H6 HMIN HSHARE HCAP2 HCAP3⟩
end F6RotationSupport
