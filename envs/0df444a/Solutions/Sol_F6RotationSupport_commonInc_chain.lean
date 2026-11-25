-- Prove2me | solution 1 for F6RotationSupport.commonInc_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:42:34.602715+00:00
-- url     : https://prove2.me/submissions/70d013db-ed1b-4ef5-bf27-793808471862

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_support_subset_supportUnion
import Theorems.Thm_F6RotationSupport_supports_disjoint_of_incomparable
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
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    {alpha beta : R} (hab : alpha < beta) :
    F6ConvexWindow.Chain (commonInc alpha beta) := by
  intro gamma hgamma delta hdelta
  by_contra hcomp
  have hinc : F6ConvexWindow.IncRel gamma delta :=
    ⟨fun h => hcomp (Or.inl h), fun h => hcomp (Or.inr h)⟩
  have hdisj := supports_disjoint_of_incomparable supp HSHARE hinc
  have hsum := card_union_of_disjoint hdisj
  have hsub : supp gamma ∪ supp delta ⊆ supportUnion supp (commonInc alpha beta) :=
    union_subset (support_subset_supportUnion supp hgamma)
      (support_subset_supportUnion supp hdelta)
  have hcount := card_le_card hsub
  have hgamma_min := HMIN gamma
  have hdelta_min := HMIN delta
  have hthree := card_commonInc_supportUnion_le_three supp H6 HSHARE HCAP2 hab
  omega
end F6RotationSupport
