-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.utilityQ_eq_tie_dp
-- status  : ACCEPTED   (disprove)
-- author  : @ytako6706
-- created : 2026-11-25T07:01:09.665401+00:00
-- url     : https://prove2.me/submissions/93128c1d-0f9b-4ea1-b234-86d705f2b837

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false
open CorrelatedAuctionComplexity.Main

/-- Two bidders, one bid `0`, values `1`, a single edge `{0}` of weight `1`. -/
def cxH : HDFPA (Fin 2) where
  bids := {0}
  value := fun _ => 1
  edges := [⟨{0}, 1⟩]

/-- Bidder `0` puts mass one on bid `0`; the non-participant bidder `1` puts mass zero. -/
def cxP : cxH.RatProfile := fun j _ => if j = 0 then 1 else 0

theorem solution : ¬ (∀ {n : ℕ} (H : HDFPA (Fin n)) (p : H.RatProfile) (i : Fin n),
    H.utilityQ p i =
      ∑ e : Fin H.edges.length, (H.edge e).weight *
        (if i ∈ (H.edge e).participants then
          ∑ b : H.Bid, p i b * edgeUtilityDP H p e i b else 0)) := by
  intro h
  have := h cxH cxP 0
  have hL : cxH.utilityQ cxP 0 = 0 := by
    unfold HDFPA.utilityQ
    refine Finset.sum_eq_zero (fun e _ => ?_)
    rw [Finset.sum_eq_zero (fun b _ => ?_), mul_zero]
    rw [Fin.prod_univ_two]
    simp [cxP]
  rw [hL] at this
  have hlen : cxH.edges.length = 1 := rfl
  have hR : (∑ e : Fin cxH.edges.length, (cxH.edge e).weight *
        (if (0 : Fin 2) ∈ (cxH.edge e).participants then
          ∑ b : cxH.Bid, cxP 0 b * edgeUtilityDP cxH cxP e 0 b else 0)) = 1 := by
    have he : ∀ e : Fin cxH.edges.length, cxH.edge e = ⟨{0}, 1⟩ := by
      rintro ⟨k, hk⟩
      have hk0 : k = 0 := by simp [cxH] at hk; omega
      subst hk0
      rfl
    have hb : ∀ b : cxH.Bid, b.val = 0 := fun b => by
      have := b.property; simpa [cxH] using this
    have hDP : ∀ (e : Fin cxH.edges.length) (b : cxH.Bid),
        edgeUtilityDP cxH cxP e 0 b = 1 := by
      intro e b
      unfold edgeUtilityDP
      rw [he e]
      have hv : cxH.value 0 = 1 := rfl
      simp [hb b, tieTable, hv, tieStep]
    haveI : Unique (Fin cxH.edges.length) := by rw [hlen]; infer_instance
    have hBid : Unique cxH.Bid := ⟨⟨⟨0, by simp [cxH]⟩⟩, fun b => Subtype.ext (hb b)⟩
    rw [Fintype.sum_unique, he, Fintype.sum_unique]
    simp [hDP, cxP]
  rw [hR] at this
  exact zero_ne_one this
