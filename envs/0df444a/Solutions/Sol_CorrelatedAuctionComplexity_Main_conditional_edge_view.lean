-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.conditional_edge_view
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:46.621545+00:00
-- url     : https://prove2.me/submissions/684990c2-f23e-4554-a5dc-6ef47b58e5f3

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

open CorrelatedAuctionComplexity.Main

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 1) (η : ℝ) (hη : 0 ≤ η)
    (σ : H.Profile) (hσ : H.Legal σ) :
    H.IsNE η σ ↔ ∀ i b, b.val ≤ H.value i →
      H.conditionalUtility (deviation σ i b) i - η ≤ H.conditionalUtility σ i := by
  classical
  rcases hH with ⟨hN, hzero, hbid, hvalue, hwf, hinc⟩
  have hweight (k : Fin H.edges.length) : 0 < ((H.edge k).weight : ℝ) := by
    exact_mod_cast (hwf (H.edge k) (List.getElem_mem _)).2
  have hW (i : N) : 0 < H.incidentWeight i := by
    obtain ⟨e, he, hie⟩ := hinc i
    obtain ⟨k, rfl⟩ := List.mem_iff_get.mp he
    have hie' : i ∈ (H.edge k).participants := by
      simpa [HDFPA.edge] using hie
    apply Finset.sum_pos'
    · intro k hk
      split_ifs with hik
      · exact (hweight k).le
      · exact le_rfl
    · refine ⟨k, Finset.mem_univ _, ?_⟩
      rw [if_pos hie']
      exact hweight k
  have hcond (p : H.Profile) (i : N) :
      H.conditionalUtility p i = H.utility p i / H.incidentWeight i := by
    unfold HDFPA.conditionalUtility HDFPA.utility
    calc
      (∑ e : Fin H.edges.length,
          if i ∈ (H.edge e).participants then
            H.edgeUtility e p i / H.incidentWeight i else 0) =
          ∑ e : Fin H.edges.length,
            (if i ∈ (H.edge e).participants then H.edgeUtility e p i else 0) /
              H.incidentWeight i := by
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ = (∑ e : Fin H.edges.length,
            if i ∈ (H.edge e).participants then H.edgeUtility e p i else 0) /
              H.incidentWeight i := by rw [Finset.sum_div]
      _ = (∑ e : Fin H.edges.length, H.edgeUtility e p i) /
              H.incidentWeight i := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs with hik
        · rfl
        · simp [HDFPA.edgeUtility, expectation, singlePayoff, hik]
  constructor
  · intro hne i b hb
    have hmain := hne.2 i b hb
    rw [hcond, hcond]
    unfold HDFPA.pureUtility at hmain
    calc
      H.utility (deviation σ i b) i / H.incidentWeight i - η =
          (H.utility (deviation σ i b) i - η * H.incidentWeight i) /
            H.incidentWeight i := by
              field_simp [(hW i).ne']
      _ ≤ H.utility σ i / H.incidentWeight i :=
        (div_le_div_iff_of_pos_right (hW i)).2 hmain
  · intro hc
    refine ⟨hσ, ?_⟩
    intro i b hb
    have hmain := hc i b hb
    rw [hcond, hcond] at hmain
    unfold HDFPA.pureUtility
    calc
      H.utility (deviation σ i b) i - η * H.incidentWeight i =
          (H.utility (deviation σ i b) i / H.incidentWeight i - η) *
            H.incidentWeight i := by
              field_simp [(hW i).ne']
      _ ≤ (H.utility σ i / H.incidentWeight i) * H.incidentWeight i :=
        mul_le_mul_of_nonneg_right hmain (hW i).le
      _ = H.utility σ i := div_mul_cancel₀ _ (hW i).ne'
