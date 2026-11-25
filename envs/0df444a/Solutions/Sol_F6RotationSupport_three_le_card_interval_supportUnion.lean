-- Prove2me | solution 1 for F6RotationSupport.three_le_card_interval_supportUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:27:49.543438+00:00
-- url     : https://prove2.me/submissions/6feb1118-a064-4851-9b03-ecda6c276f98

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_interval_orderConvex
import Theorems.Thm_F6RotationSupport_two_le_card_interval

set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]
namespace F6RotationSupport
theorem _root_.solution (supp : R → Finset M)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    {alpha beta : R} (hab : alpha < beta) :
    3 ≤ (supportUnion supp (interval alpha beta)).card := by
  have htwo := two_le_card_interval hab
  by_contra h
  have hsmall : (supportUnion supp (interval alpha beta)).card ≤ 2 := by omega
  have hone := HCAP2 (interval alpha beta) (interval_orderConvex alpha beta) hsmall
  omega
end F6RotationSupport
