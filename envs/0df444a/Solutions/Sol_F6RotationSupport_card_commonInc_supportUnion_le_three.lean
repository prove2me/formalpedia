-- Prove2me | solution 1 for F6RotationSupport.card_commonInc_supportUnion_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:36:15.171428+00:00
-- url     : https://prove2.me/submissions/71662fb1-eabe-485c-8669-ae7c45f20af9

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_interval_commonInc_supportUnion_disjoint
import Theorems.Thm_F6RotationSupport_three_le_card_interval_supportUnion

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
    {alpha beta : R} (hab : alpha < beta) :
    (supportUnion supp (commonInc alpha beta)).card ≤ 3 := by
  have hthree := three_le_card_interval_supportUnion supp HCAP2 hab
  have hdisj := interval_commonInc_supportUnion_disjoint supp HSHARE alpha beta
  have hsum := card_union_of_disjoint hdisj
  have hmen := (supportUnion supp (interval alpha beta) ∪
    supportUnion supp (commonInc alpha beta)).card_le_univ
  omega
end F6RotationSupport
