-- Prove2me | solution 1 for CClosedGraphs.LowerBound.claim_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:32:46.246856+00:00
-- url     : https://prove2.me/submissions/408ecc44-a8ed-4bba-a030-e9ce4fb5585d

import Mathlib
import Definitions.Def_CClosedGraphs_LowerBound_Setting

set_option autoImplicit false
open Finset

theorem no_tri {V : Type*} (H : SimpleGraph V) (hH : 5 ≤ H.egirth) (a b c : V)
    (h1 : H.Adj a b) (h2 : H.Adj b c) (h3 : H.Adj c a) : False := by
  have hab := h1.ne
  have hbc := h2.ne
  have hca := h3.ne
  have hcyc : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3 SimpleGraph.Walk.nil))).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    refine ⟨?_, by simp, ?_⟩
    · simp [SimpleGraph.Walk.isTrail_def, Sym2.eq_iff, hab, hbc, hca, hab.symm, hbc.symm, hca.symm]
    · simp [hab, hbc, hca, hab.symm, hbc.symm, hca.symm]
  have := hH.trans (SimpleGraph.egirth_le_length hcyc)
  simp at this
  norm_cast at this

theorem no_c4 {V : Type*} (H : SimpleGraph V) (hH : 5 ≤ H.egirth) (u a v b : V)
    (h1 : H.Adj u a) (h2 : H.Adj a v) (h3 : H.Adj v b) (h4 : H.Adj b u) (hab : a ≠ b) (huv : u ≠ v) :
    False := by
  have h1' := h1.ne
  have h2' := h2.ne
  have h3' := h3.ne
  have h4' := h4.ne
  have hcyc : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3 (SimpleGraph.Walk.cons h4 SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    refine ⟨?_, by simp, ?_⟩
    · simp [SimpleGraph.Walk.isTrail_def, Sym2.eq_iff, h1', h2', h3', h4', h1'.symm, h2'.symm, h3'.symm, h4'.symm, hab, hab.symm, huv, huv.symm]
    · simp [h1', h2', h3', h4', h1'.symm, h2'.symm, h3'.symm, h4'.symm, hab, hab.symm, huv, huv.symm]
  have := hH.trans (SimpleGraph.egirth_le_length hcyc)
  simp at this
  norm_cast at this

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (h : ℕ)
    (hh : 1 ≤ h) (hH : 5 ≤ H.egirth) : CClosedGraphs.Peeling.IsCClosed (2 * h) (CClosedGraphs.LowerBound.blowUp H h) := by
  classical
  intro u v huv hcn
  by_contra hnadj
  obtain ⟨x, i⟩ := u
  obtain ⟨y, j⟩ := v
  have hxy : x ≠ y := by
    rintro rfl
    apply hnadj
    refine ⟨?_, Or.inl rfl⟩
    intro hij
    have hij' : i = j := hij
    exact huv (by rw [hij'])
  let Z : Finset V := Finset.univ.filter (fun z => (z = x ∨ H.Adj x z) ∧ (z = y ∨ H.Adj y z))
  have hZ : Z.card ≤ 2 := by
    by_cases hadj : H.Adj x y
    · have : Z ⊆ {x, y} := by
        intro z hz
        simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hz with ⟨hz1 | hz1, hz2 | hz2⟩
        · exact Or.inl hz1
        · exact Or.inl hz1
        · exact Or.inr hz2
        · exact absurd (no_tri H hH x y z hadj hz2 hz1.symm) id
      exact (Finset.card_le_card this).trans Finset.card_le_two
    · have : Z.card ≤ 1 := by
        rw [Finset.card_le_one]
        have key : ∀ z ∈ Z, H.Adj x z ∧ H.Adj y z := by
          intro z hz
          simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          rcases hz with ⟨hz1 | hz1, hz2 | hz2⟩
          · exact absurd (hz1.symm.trans hz2) hxy
          · subst hz1; exact absurd hz2.symm hadj
          · subst hz2; exact absurd hz1 hadj
          · exact ⟨hz1, hz2⟩
        intro a ha b hb
        by_contra hab
        obtain ⟨ha1, ha2⟩ := key a ha
        obtain ⟨hb1, hb2⟩ := key b hb
        exact no_c4 H hH x a y b ha1 ha2.symm hb2 hb1.symm hab hxy
      omega
  have hsub : (CClosedGraphs.LowerBound.blowUp H h).commonNeighbors (x, i) (y, j) ⊆
      ↑(Z ×ˢ (Finset.univ.erase i)) := by
    rintro ⟨z, k⟩ hz
    rw [SimpleGraph.mem_commonNeighbors] at hz
    obtain ⟨⟨hk1, hz1⟩, ⟨hk2, hz2⟩⟩ := hz
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Z, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase, ne_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hz1.imp Eq.symm id
    · exact hz2.imp Eq.symm id
    · exact ⟨Ne.symm hk1, trivial⟩
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin] at h1
  have h2 : Z.card * (h - 1) ≤ 2 * (h - 1) := Nat.mul_le_mul_right _ hZ
  omega
