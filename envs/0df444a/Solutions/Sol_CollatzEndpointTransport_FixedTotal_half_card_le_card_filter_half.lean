-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.half_card_le_card_filter_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:13.932009+00:00
-- url     : https://prove2.me/submissions/f169659e-4c69-4be2-82f8-8e0f304ba74a

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_filter_lt_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Finset ℕ) :
    S.card - S.card / 2 ≤
      (S.filter fun q => S.card / 2 ≤ q).card := by
  let low := S.filter fun q => q < S.card / 2
  let high := S.filter fun q => S.card / 2 ≤ q
  have hlow : low.card ≤ S.card / 2 := by
    exact card_filter_lt_le S (S.card / 2)
  have hdisj : Disjoint low high := by
    refine Finset.disjoint_left.mpr ?_
    intro q hqLow hqHigh
    exact (not_lt_of_ge (Finset.mem_filter.mp hqHigh).2)
      (Finset.mem_filter.mp hqLow).2
  have hunion : low ∪ high = S := by
    ext q
    simp only [low, high, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((⟨hq, _⟩) | (⟨hq, _⟩)) <;> exact hq
    · intro hq
      exact (lt_or_ge q (S.card / 2)).elim
        (fun hlt => Or.inl ⟨hq, hlt⟩)
        (fun hge => Or.inr ⟨hq, hge⟩)
  have hpart : low.card + high.card = S.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  change S.card - S.card / 2 ≤ high.card
  omega
end CollatzEndpointTransport.FixedTotal
