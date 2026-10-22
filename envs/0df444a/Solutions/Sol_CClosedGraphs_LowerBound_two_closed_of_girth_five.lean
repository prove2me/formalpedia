-- Prove2me | solution 1 for CClosedGraphs.LowerBound.two_closed_of_girth_five
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:21:28.34284+00:00
-- url     : https://prove2.me/submissions/00e58e1b-4a99-4ef7-bf50-16ba33b0aa4e

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

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

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (hH : 5 ≤ H.egirth) : CClosedGraphs.Peeling.IsCClosed 2 H ∧ H.edgeSet.ncard ≤ CClosedGraphs.Peeling.numMaxCliques H := by
  constructor
  · intro u v huv h2
    exfalso
    have hfin : (H.commonNeighbors u v).Finite := Set.toFinite _
    have h1 : 1 < (H.commonNeighbors u v).ncard := by omega
    obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff hfin).1 h1
    rw [SimpleGraph.mem_commonNeighbors] at ha hb
    exact no_c4 H hH u a v b ha.1 ha.2.symm hb.2 hb.1.symm hab huv
  · classical
    let f : Sym2 V → Finset V := fun e => Finset.univ.filter (· ∈ e)
    have hf : Function.Injective f := by
      intro e e' h
      apply Sym2.ext
      intro z
      have := congrArg (fun s : Finset V => z ∈ s) h
      simpa [f] using this
    have hsub : f '' H.edgeSet ⊆ ↑(CClosedGraphs.Peeling.maxCliquesIn H Set.univ) := by
      rintro _ ⟨e, he, rfl⟩
      induction e using Sym2.ind with
      | h x y =>
        have hxy : H.Adj x y := he
        simp only [Finset.mem_coe, CClosedGraphs.Peeling.maxCliquesIn, Finset.mem_filter, Finset.mem_univ, true_and]
        have hfe : f s(x, y) = {x, y} := by
          ext z; simp [f]
        rw [hfe]
        refine ⟨⟨Set.subset_univ _, ?_⟩, ?_⟩
        · intro p hp q hq hpq
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
          rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
          · exact absurd rfl hpq
          · exact hxy
          · exact hxy.symm
          · exact absurd rfl hpq
        · intro T hT hsub'
          obtain ⟨-, hcl⟩ := hT
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton]
          by_contra hne
          push_neg at hne
          have hx : x ∈ T := hsub' (by simp)
          have hy : y ∈ T := hsub' (by simp)
          have hzx : H.Adj z x := hcl (by exact_mod_cast hz) (by exact_mod_cast hx) hne.1
          have hzy : H.Adj z y := hcl (by exact_mod_cast hz) (by exact_mod_cast hy) hne.2
          exact no_tri H hH x y z hxy hzy.symm hzx
    calc H.edgeSet.ncard = (f '' H.edgeSet).ncard := (Set.ncard_image_of_injective _ hf).symm
      _ ≤ (↑(CClosedGraphs.Peeling.maxCliquesIn H Set.univ) : Set (Finset V)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = CClosedGraphs.Peeling.numMaxCliques H := by
          rw [Set.ncard_coe_finset]; rfl
