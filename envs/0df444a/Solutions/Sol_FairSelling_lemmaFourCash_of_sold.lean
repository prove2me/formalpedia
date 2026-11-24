-- Prove2me | solution 1 for FairSelling.lemmaFourCash_of_sold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:02:47.618163+00:00
-- url     : https://prove2.me/submissions/05b8670a-146c-4b70-bb13-f5508561d7a9

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_lemmaFour_of_no_undervaluation
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (h : LemmaFourCashSold G) : LemmaFourCash G := by
  classical
  intro w p hw hp hnobig K S m hKS hm0 hmS hScard hKcard hprice hrej
  rcases S.eq_empty_or_nonempty with rfl | ⟨f, hfS⟩
  · exact lemmaFour_of_no_undervaluation w p hw hp hnobig K ∅ m hKS hmS (by simp [vbarSum]) hrej
  · have hSeq : S = {f} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hfS, fun x hx => Finset.card_le_one.mp hScard x hx f hfS⟩
    subst hSeq
    have hKone : K.card ≤ 1 := by
      rcases hKcard with hc | hc
      · exact hc
      · exact absurd hc (Finset.singleton_ne_empty f)
    have hfK : f ∉ K :=
      fun hmem => (Finset.disjoint_left.mp hKS hmem) (Finset.mem_singleton_self f)
    have hmf : m ≤ p f := by simpa using hmS
    simpa using h w p hw hp hnobig K f m hfK hm0 hmf hKone
      (hprice f (Finset.mem_singleton_self f)) hrej
end FairSelling
