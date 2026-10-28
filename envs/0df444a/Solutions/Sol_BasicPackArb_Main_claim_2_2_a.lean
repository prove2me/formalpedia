-- Prove2me | solution 1 for BasicPackArb.Main.claim_2_2_a
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:20:33.557928+00:00
-- url     : https://prove2.me/submissions/5c5c1595-8fa1-4327-9fe6-4b7a0a3ebd1b

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph
import Definitions.Def_BasicPackArb_Main_ProofObjects

open BasicPackArb.Main in
theorem solution {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ)
    (hconn : MConnected D π M) (X : Finset V) (hX : IsTight D π M X) (v : V) (hvX : v ∈ X)
    (Y : Finset V) (hY : IsTight D π M Y) (hvY : v ∈ Y) :
    IsTight D π M (X ∩ Y) ∧ IsTight D π M (X ∪ Y) ∧
      M.eRk (π ⁻¹' (X : Set V) ∩ π ⁻¹' (Y : Set V)) + M.eRk (π ⁻¹' (X : Set V) ∪ π ⁻¹' (Y : Set V))
        = M.eRk (π ⁻¹' (X : Set V)) + M.eRk (π ⁻¹' (Y : Set V)) := by
  classical
  have hfin : ∀ Z : Set S, M.eRk Z ≠ ⊤ := fun Z =>
    Matroid.eRk_ne_top_iff.mpr (M.isRkFinite_of_finite (Set.toFinite Z))
  -- in-degree submodularity
  have hdeg : D.inDeg (X ∩ Y) + D.inDeg (X ∪ Y) ≤ D.inDeg X + D.inDeg Y := by
    unfold Digraph.inDeg Digraph.enteringArcs
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    by_cases h1 : D.tail a ∈ X <;> by_cases h2 : D.tail a ∈ Y <;>
      by_cases h3 : D.head a ∈ X <;> by_cases h4 : D.head a ∈ Y <;>
      simp [h1, h2, h3, h4]
  have hsub := M.eRk_inter_add_eRk_union_le (π ⁻¹' (X : Set V)) (π ⁻¹' (Y : Set V))
  have hcI := hconn (X ∩ Y) ⟨v, Finset.mem_inter.mpr ⟨hvX, hvY⟩⟩
  have hcU := hconn (X ∪ Y) ⟨v, Finset.mem_union_left _ hvX⟩
  unfold IsTight
  rw [Finset.coe_inter, Set.preimage_inter] at hcI ⊢
  rw [Finset.coe_union, Set.preimage_union] at hcU ⊢
  unfold IsTight at hX hY
  obtain ⟨rX, hrX⟩ := ENat.ne_top_iff_exists.mp (hfin (π ⁻¹' (X : Set V)))
  obtain ⟨rY, hrY⟩ := ENat.ne_top_iff_exists.mp (hfin (π ⁻¹' (Y : Set V)))
  obtain ⟨rI, hrI⟩ := ENat.ne_top_iff_exists.mp
    (hfin (π ⁻¹' (X : Set V) ∩ π ⁻¹' (Y : Set V)))
  obtain ⟨rU, hrU⟩ := ENat.ne_top_iff_exists.mp
    (hfin (π ⁻¹' (X : Set V) ∪ π ⁻¹' (Y : Set V)))
  obtain ⟨R, hR⟩ := ENat.ne_top_iff_exists.mp (hfin Set.univ)
  rw [← hrX, ← hR] at hX
  rw [← hrY, ← hR] at hY
  rw [← hrI, ← hR] at hcI
  rw [← hrU, ← hR] at hcU
  rw [← hrI, ← hrU, ← hrX, ← hrY] at hsub
  rw [← hrI, ← hrU, ← hrX, ← hrY, ← hR]
  norm_cast at hX hY hcI hcU hsub ⊢
  refine ⟨?_, ?_, ?_⟩ <;> omega
