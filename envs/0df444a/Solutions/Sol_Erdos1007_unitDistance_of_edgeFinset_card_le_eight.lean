-- Prove2me | solution 1 for Erdos1007.unitDistance_of_edgeFinset_card_le_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:22.154863+00:00
-- url     : https://prove2.me/submissions/c3bbb299-8dd9-4e3b-983b-23e68f5b8043

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Erdos1007_Geometry_CompleteMinusEdge
public import Definitions.Def_Erdos1007_Geometry_Reattach
public import Definitions.Def_Erdos1007_Geometry_UnitDistanceComap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos1007_Geometry_EightEdges
public import Theorems.Thm_Erdos1007_completeGraph_five_deleteEdge_unitDistance
public import Theorems.Thm_Erdos1007_unitDistance_extend_degree_le_two
public import Theorems.Thm_Erdos1007_unitDistance_of_embedding
public import Theorems.Thm_Erdos1007_unitDistance_of_le

section
namespace Erdos1007
universe u
open SimpleGraph Metric
private lemma card_subtype_ne {V : Type*} [Fintype V] [DecidableEq V] (u : V) :
    Fintype.card {v : V // v ≠ u} = Fintype.card V - 1 := by
  rw [Fintype.card_subtype_compl (fun v => v = u), Fintype.card_subtype_eq]
private lemma card_edgeFinset_induce_ne {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (u : V) :
    (G.induce {v | v ≠ u}).edgeFinset.card = G.edgeFinset.card - G.degree u := by
  rw [← G.card_edgeFinset_deleteIncidenceSet u,
    ← G.card_edgeFinset_induce_compl_singleton u]
  rfl
private lemma exists_equiv_sending_pair {V : Type*} [Fintype V]
    (hcard : Fintype.card V = 5) {p q : V} (hpq : p ≠ q) :
    ∃ e : V ≃ Fin 5, e p = 3 ∧ e q = 4 := by
  classical
  let e0 : V ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
  let e1 : V ≃ Fin 5 := Equiv.setValue e0 p 3
  have he1 : e1 p = 3 := Equiv.setValue_eq e0 p 3
  let e2 : V ≃ Fin 5 := Equiv.setValue e1 q 4
  have he2q : e2 q = 4 := Equiv.setValue_eq e1 q 4
  have he2p : e2 p = 3 := by
    have hsym : p ≠ e1.symm (4 : Fin 5) := by
      intro hps
      have : e1 p = 4 := by
        rw [hps]
        exact e1.apply_symm_apply 4
      rw [he1] at this
      exact absurd this (by decide : (3 : Fin 5) ≠ 4)
    simp only [e2, Equiv.setValue, Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hpq hsym]
    exact he1
  exact ⟨e2, he2p, he2q⟩
private lemma unitDistance_of_minDegree_on_four {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hcard : Fintype.card V = 4)
    (hmin : ∀ v, 3 ≤ G.degree v) :
    ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ u v, G.Adj u v → dist (f u) (f v) = 1 := by
  classical
  have hdeg : ∀ v, G.degree v = 3 := by
    intro v
    have hge := hmin v
    have hlt := G.degree_lt_card_verts v
    rw [hcard] at hlt
    omega
  have htop : G = ⊤ := by
    rw [eq_top_iff_forall_isUniversal]
    intro v
    rw [← G.degree_eq_card_sub_one v, hdeg v, hcard]
  let e : V ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  let f : V ↪ Fin 5 := e.toEmbedding.trans Fin.castSuccEmb
  have hcoe (v : V) : f v = Fin.castSucc (e v) := by
    simp [f, Function.Embedding.trans_apply, Fin.coe_castSuccEmb]
  have hne4 (v : V) : f v ≠ 4 := by
    rw [hcoe v]
    have hlast : (4 : Fin 5) = Fin.last 4 := by decide
    rw [hlast]
    exact (Fin.castSucc_lt_last (e v)).ne
  refine unitDistance_of_embedding (φ := ?_) completeGraph_five_deleteEdge_unitDistance
  refine ⟨f, ?_⟩
  intro a b
  rw [htop]
  simp only [top_adj, deleteEdges_adj]
  constructor
  · rintro ⟨hne, _⟩
    exact f.injective.ne_iff.mp hne
  · intro hab
    refine ⟨f.injective.ne hab, ?_⟩
    intro hs
    rw [Set.mem_singleton_iff] at hs
    rcases Sym2.eq_iff.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hne4 b hb
    · exact hne4 a ha
private lemma exists_compl_matching_of_five {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hcard : Fintype.card V = 5)
    (hmin : ∀ v, 3 ≤ G.degree v) (hedge : G.edgeFinset.card ≤ 8) :
    ∃ p q : V, Gᶜ.Adj p q ∧ ∃ r s : V, Gᶜ.Adj r s ∧
      ({p, q, r, s} : Finset V).card = 4 ∧
      Gᶜ.edgeFinset = {s(p, q), s(r, s)} := by
  have hsumEq : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hconst : ∑ v : V, (3 : ℕ) = 3 * Fintype.card V := by
    rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]
    exact mul_comm _ _
  have hlower : 3 * Fintype.card V ≤ ∑ v, G.degree v := by
    rw [← hconst]
    exact Finset.sum_le_sum fun v _ => hmin v
  have hedge8 : G.edgeFinset.card = 8 := by
    have h15 : 3 * 5 ≤ 2 * G.edgeFinset.card := by
      have h3 : 3 * 5 ≤ ∑ v, G.degree v := by
        simpa [hcard] using hlower
      rwa [hsumEq] at h3
    omega
  have hsum16 : ∑ v, G.degree v = 16 := by
    rw [hsumEq, hedge8]
  have h34 : ∀ v, G.degree v = 3 ∨ G.degree v = 4 := by
    intro v
    have hge := hmin v
    have hlt := G.degree_lt_card_verts v
    rw [hcard] at hlt
    omega
  have hconst15 : ∑ v : V, (3 : ℕ) = 15 := by
    rw [hconst, hcard]
  have hdiff : ∑ v, (G.degree v - 3) = 1 := by
    have hsplit := Finset.sum_tsub_distrib (Finset.univ : Finset V)
      (f := fun v => G.degree v) (g := fun _ => (3 : ℕ)) (fun v _ => hmin v)
    rw [hsplit, hsum16, hconst15]
  obtain ⟨w, hw1⟩ : ∃ w, G.degree w - 3 = 1 := by
    refine Classical.byContradiction fun hnone => ?_
    have hzero : ∀ v, G.degree v - 3 = 0 := by
      intro v
      rcases h34 v with hv | hv
      · simp [hv]
      · exact False.elim (hnone ⟨v, by simp [hv]⟩)
    have : ∑ v, (G.degree v - 3) = 0 := Finset.sum_eq_zero fun v _ => hzero v
    rw [hdiff] at this
    exact Nat.one_ne_zero this
  have hw : G.degree w = 4 := by omega
  have herase : ∑ x ∈ Finset.univ.erase w, (G.degree x - 3) = 0 := by
    have hadd := Finset.add_sum_erase (Finset.univ : Finset V) (fun x => G.degree x - 3)
      (Finset.mem_univ w)
    rw [hw1, hdiff] at hadd
    omega
  have hrest : ∀ v, v ≠ w → G.degree v = 3 := by
    intro v hv
    have hv0 : G.degree v - 3 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp herase v
        (by simp [hv])
    rcases h34 v with h | h
    · exact h
    · omega
  have hdegC (v : V) : Gᶜ.degree v = 4 - G.degree v := by
    rw [G.degree_compl, hcard]
  have hdegCw : Gᶜ.degree w = 0 := by
    rw [hdegC, hw]
  have hdegCrest (v : V) (hv : v ≠ w) : Gᶜ.degree v = 1 := by
    rw [hdegC, hrest v hv]
  have hdegC_le (v : V) : Gᶜ.degree v ≤ 1 := by
    by_cases hv : v = w
    · rw [hv, hdegCw]
      exact Nat.zero_le _
    · rw [hdegCrest v hv]
  have hsumC : ∑ v, Gᶜ.degree v = 4 := by
    have hadd := Finset.add_sum_erase (Finset.univ : Finset V) (fun v => Gᶜ.degree v)
      (Finset.mem_univ w)
    rw [hdegCw] at hadd
    have heraseC : ∑ v ∈ Finset.univ.erase w, Gᶜ.degree v = 4 := by
      rw [Finset.sum_const_nat (fun v hv => hdegCrest v ((Finset.mem_erase.mp hv).1)),
        Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, hcard]
    omega
  have hcardC : Gᶜ.edgeFinset.card = 2 := by
    have hsumCeq : ∑ v, Gᶜ.degree v = 2 * Gᶜ.edgeFinset.card :=
      Gᶜ.sum_degrees_eq_twice_card_edges
    omega
  obtain ⟨e₁, e₂, he₁₂, hes⟩ := Finset.card_eq_two.mp hcardC
  have edgeEnds (e : Sym2 V) (he : e ∈ Gᶜ.edgeFinset) :
      ∃ a b, e = s(a, b) ∧ Gᶜ.Adj a b := by
    induction e using Sym2.ind with
    | h a b =>
      exact ⟨a, b, rfl,
        (mem_edgeSet (G := Gᶜ)).mp ((mem_edgeFinset (G := Gᶜ)).mp he)⟩
  obtain ⟨p, q, he₁, hpqAdj⟩ := edgeEnds e₁ (by simp [hes])
  obtain ⟨r, s, he₂, hrsAdj⟩ := edgeEnds e₂ (by simp [hes])
  subst he₁
  subst he₂
  have hpq : p ≠ q := ((compl_adj G p q).mp hpqAdj).1
  have hrs : r ≠ s := ((compl_adj G r s).mp hrsAdj).1
  have huniq {a b c : V} (hab : Gᶜ.Adj a b) (hac : Gᶜ.Adj a c) : b = c := by
    have hcardN : (Gᶜ.neighborFinset a).card ≤ 1 := by
      rw [Gᶜ.card_neighborFinset_eq_degree]
      exact hdegC_le a
    have hb : b ∈ Gᶜ.neighborFinset a := (Gᶜ.mem_neighborFinset a b).mpr hab
    have hc : c ∈ Gᶜ.neighborFinset a := (Gᶜ.mem_neighborFinset a c).mpr hac
    exact (Finset.card_le_one.mp hcardN) b hb c hc
  have hpr : p ≠ r := by
    intro h
    have hqs : q = s := huniq (h.symm ▸ hpqAdj) hrsAdj
    exact he₁₂ (by rw [h, hqs])
  have hps : p ≠ s := by
    intro h
    have hqr : q = r := huniq (h.symm ▸ hpqAdj) hrsAdj.symm
    exact he₁₂ (by rw [h, hqr, Sym2.eq_swap])
  have hqr : q ≠ r := by
    intro h
    have hps' : p = s := huniq hpqAdj.symm (h.symm ▸ hrsAdj)
    exact he₁₂ (by rw [h, hps', Sym2.eq_swap])
  have hqs : q ≠ s := by
    intro h
    have hpr' : p = r := huniq hpqAdj.symm (h.symm ▸ hrsAdj.symm)
    exact he₁₂ (by rw [h, hpr'])
  have hfour : ({p, q, r, s} : Finset V).card = 4 :=
    Finset.card_eq_four.mpr ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩
  exact ⟨p, q, hpqAdj, r, s, hrsAdj, hfour, hes⟩
private lemma unitDistance_of_minDegree_on_five {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hcard : Fintype.card V = 5)
    (hmin : ∀ v, 3 ≤ G.degree v) (hedge : G.edgeFinset.card ≤ 8) :
    ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ u v, G.Adj u v → dist (f u) (f v) = 1 := by
  classical
  obtain ⟨p, q, hpqAdj, _⟩ := exists_compl_matching_of_five hcard hmin hedge
  have hpq : p ≠ q := ((compl_adj G p q).mp hpqAdj).1
  have hnot : ¬ G.Adj p q := ((compl_adj G p q).mp hpqAdj).2
  obtain ⟨e, hep, heq⟩ := exists_equiv_sending_pair hcard hpq
  have hle : G.map e.toEmbedding ≤
      (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)} := by
    intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨a, b, hab, rfl, rfl⟩ := hxy
    rw [deleteEdges_adj, top_adj]
    refine ⟨e.injective.ne hab.ne, ?_⟩
    intro hs
    rw [Set.mem_singleton_iff] at hs
    rcases Sym2.eq_iff.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have ha' : a = p := e.injective (ha.trans hep.symm)
      have hb' : b = q := e.injective (hb.trans heq.symm)
      exact hnot (ha' ▸ hb' ▸ hab)
    · have ha' : a = q := e.injective (ha.trans heq.symm)
      have hb' : b = p := e.injective (hb.trans hep.symm)
      exact hnot (ha' ▸ hb' ▸ hab.symm)
  exact unitDistance_of_embedding (Embedding.map e.toEmbedding G)
    (unitDistance_of_le hle completeGraph_five_deleteEdge_unitDistance)
attribute [-instance] SimpleGraph.fintypeEdgeSetSup in
/-- Delete a vertex of degree at most two and reattach it by the inductive hypothesis. -/
private lemma unitDistance_delete_low_degree {n : ℕ} {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u : V} (hu : G.degree u ≤ 2)
    (hmeas : Fintype.card V + G.edgeFinset.card ≤ n + 1) (hedge : G.edgeFinset.card ≤ 8)
    (ih : ∀ {W : Type u} [Fintype W] {H : SimpleGraph W} [DecidableRel H.Adj],
      Fintype.card W + H.edgeFinset.card ≤ n → H.edgeFinset.card ≤ 8 →
      ∃ f : W → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
        ∀ a b, H.Adj a b → dist (f a) (f b) = 1) :
    ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ a b, G.Adj a b → dist (f a) (f b) = 1 := by
  classical
  have hdeg_le_edges : G.degree u ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset u
  have hcpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have glue (H : SimpleGraph {v // v ≠ u}) [DecidableRel H.Adj]
      (hsub : ∀ ⦃a b : {v // v ≠ u}⦄,
        (G.induce {v | v ≠ u}).Adj a b → H.Adj a b)
      (hextra : ∀ ⦃a b : {v // v ≠ u}⦄, G.degree u = 2 → a.1 ∈ G.neighborSet u →
        b.1 ∈ G.neighborSet u → a ≠ b → H.Adj a b)
      (hmeas' : Fintype.card {v // v ≠ u} + H.edgeFinset.card ≤ n)
      (hEle : H.edgeFinset.card ≤ 8) :
      ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
        ∀ a b, G.Adj a b → dist (f a) (f b) = 1 := by
    classical
    obtain ⟨f, hfInj, hfDist⟩ :=
      ih (W := {v // v ≠ u}) (H := H) hmeas' hEle
    refine unitDistance_extend_degree_le_two hu ⟨f, hfInj, ?_⟩
    intro a b hcond
    rcases hcond with hadj | ⟨h2, ha, hb, hab⟩
    · exact hfDist a b (hsub hadj)
    · exact hfDist a b (hextra h2 ha hb hab)
  obtain hdeg | hdeg | hdeg : G.degree u = 0 ∨ G.degree u = 1 ∨ G.degree u = 2 := by
    omega
  · let H : SimpleGraph {v // v ≠ u} := G.induce {v | v ≠ u}
    have hmeas' : Fintype.card {v // v ≠ u} + H.edgeFinset.card ≤ n := by
      rw [card_subtype_ne u, card_edgeFinset_induce_ne (G := G) u, hdeg]
      have := hcpos
      have := hdeg_le_edges
      omega
    have hEle : H.edgeFinset.card ≤ 8 := by
      rw [card_edgeFinset_induce_ne (G := G) u, hdeg]
      omega
    exact glue H (fun _ _ h => h) (fun _ _ h2 _ _ _ => by omega) hmeas' hEle
  · let H : SimpleGraph {v // v ≠ u} := G.induce {v | v ≠ u}
    have hmeas' : Fintype.card {v // v ≠ u} + H.edgeFinset.card ≤ n := by
      rw [card_subtype_ne u, card_edgeFinset_induce_ne (G := G) u, hdeg]
      have := hcpos
      have := hdeg_le_edges
      omega
    have hEle : H.edgeFinset.card ≤ 8 := by
      rw [card_edgeFinset_induce_ne (G := G) u, hdeg]
      omega
    exact glue H (fun _ _ h => h) (fun _ _ h2 _ _ _ => by omega) hmeas' hEle
  · let G' : SimpleGraph {v // v ≠ u} := G.induce {v | v ≠ u}
    have hNcard : (G.neighborFinset u).card = 2 := by
      rw [G.card_neighborFinset_eq_degree, hdeg]
    obtain ⟨a, b, _, hN⟩ := Finset.card_eq_two.mp hNcard
    have ha : G.Adj u a := (G.mem_neighborFinset u a).mp (by simp [hN])
    have hb : G.Adj u b := (G.mem_neighborFinset u b).mp (by simp [hN])
    let a' : {v // v ≠ u} := ⟨a, ha.ne'⟩
    let b' : {v // v ≠ u} := ⟨b, hb.ne'⟩
    let E : SimpleGraph {v // v ≠ u} := fromRel fun x y => x = a' ∧ y = b'
    let H : SimpleGraph {v // v ≠ u} := G' ⊔ E
    have hHcard : H.edgeFinset.card ≤ G'.edgeFinset.card + 1 := by
      have hsub : H.edgeFinset ⊆ G'.edgeFinset ∪ {s(a', b')} := by
        intro e he
        have heSet : e ∈ H.edgeSet := (mem_edgeFinset (G := H)).mp he
        induction e using Sym2.ind with
        | h x y =>
          have hadj : H.Adj x y := (mem_edgeSet (G := H)).mp heSet
          simp only [H, sup_adj] at hadj
          rcases hadj with hG | ⟨_, hpair⟩
          · exact Finset.mem_union_left _ ((mem_edgeFinset (G := G')).mpr
              ((mem_edgeSet (G := G')).mpr hG))
          · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
            · rw [Sym2.eq_swap]
              exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hunion : (G'.edgeFinset ∪ {s(a', b')}).card ≤ G'.edgeFinset.card + 1 := by
        exact (Finset.card_union_le _ _).trans (by simp)
      exact (Finset.card_le_card hsub).trans hunion
    have hmeas' : Fintype.card {v // v ≠ u} + H.edgeFinset.card ≤ n := by
      have hG' : G'.edgeFinset.card = G.edgeFinset.card - 2 := by
        rw [card_edgeFinset_induce_ne (G := G) u, hdeg]
      have hEle' : H.edgeFinset.card ≤ G.edgeFinset.card - 1 := by
        calc
          H.edgeFinset.card ≤ G'.edgeFinset.card + 1 := hHcard
          _ = G.edgeFinset.card - 2 + 1 := by rw [hG']
          _ ≤ G.edgeFinset.card - 1 := by
            have := hdeg_le_edges
            omega
      rw [card_subtype_ne u]
      have := hcpos
      omega
    have hEle : H.edgeFinset.card ≤ 8 := by
      have hG' : G'.edgeFinset.card = G.edgeFinset.card - 2 := by
        rw [card_edgeFinset_induce_ne (G := G) u, hdeg]
      have := hdeg_le_edges
      omega
    obtain ⟨f, hfInj, hfDist⟩ := ih (W := {v // v ≠ u}) (H := H) hmeas' hEle
    refine unitDistance_extend_degree_le_two hu ⟨f, hfInj, ?_⟩
    intro x y hcond
    rcases hcond with hadj | ⟨_, hxN, hyN, hxy⟩
    · exact hfDist x y ((le_sup_left : G' ≤ H) hadj)
    · have hxab : x.1 = a ∨ x.1 = b := by
        have hxFin : x.1 ∈ G.neighborFinset u :=
          (G.mem_neighborFinset u x.1).mpr ((G.mem_neighborSet u x.1).mp hxN)
        rw [hN] at hxFin
        simpa using hxFin
      have hyab : y.1 = a ∨ y.1 = b := by
        have hyFin : y.1 ∈ G.neighborFinset u :=
          (G.mem_neighborFinset u y.1).mpr ((G.mem_neighborSet u y.1).mp hyN)
        rw [hN] at hyFin
        simpa using hyFin
      have hEadj : E.Adj x y := by
        rw [fromRel_adj]
        refine ⟨hxy, ?_⟩
        rcases hxab with hxa | hxb <;> rcases hyab with hya | hyb
        · exact absurd (Subtype.ext (hxa.trans hya.symm)) hxy
        · exact Or.inl ⟨Subtype.ext hxa, Subtype.ext hyb⟩
        · exact Or.inr ⟨Subtype.ext hya, Subtype.ext hxb⟩
        · exact absurd (Subtype.ext (hxb.trans hyb.symm)) hxy
      exact hfDist x y ((le_sup_right : E ≤ H) hEadj)
private lemma unitDistance_of_edgeFinset_card_le_eight_aux :
    ∀ (n : ℕ) {V : Type u} [Fintype V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
      Fintype.card V + G.edgeFinset.card ≤ n →
      G.edgeFinset.card ≤ 8 →
      ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1 := by
  intro n
  induction n with
  | zero =>
    rintro V _ G _ hmeas _
    have hcard0 : Fintype.card V = 0 := by omega
    have hEmpty : IsEmpty V := Fintype.card_eq_zero_iff.mp hcard0
    exact ⟨fun v => hEmpty.elim v, fun a _ => hEmpty.elim a, fun u _ _ => hEmpty.elim u⟩
  | succ n ih =>
    rintro V _ G _ hmeas hedge
    by_cases hlow : ∃ u, G.degree u ≤ 2
    · obtain ⟨u, hu⟩ := hlow
      exact unitDistance_delete_low_degree hu hmeas hedge ih
    · have hmin : ∀ u, 3 ≤ G.degree u := by
        intro u
        have : ¬ G.degree u ≤ 2 := by
          intro h
          exact hlow ⟨u, h⟩
        omega
      rcases isEmpty_or_nonempty V with hEmpty | hNonempty
      · exact ⟨fun v => hEmpty.elim v, fun a _ => hEmpty.elim a,
          fun u _ _ => hEmpty.elim u⟩
      · obtain ⟨u0⟩ := hNonempty
        have hcard_ge : 4 ≤ Fintype.card V := by
          have hge := hmin u0
          have hlt := G.degree_lt_card_verts u0
          omega
        have hsumEq : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
          G.sum_degrees_eq_twice_card_edges
        have hconst : ∑ v : V, (3 : ℕ) = 3 * Fintype.card V := by
          rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]
          exact mul_comm _ _
        have hlower : 3 * Fintype.card V ≤ ∑ v, G.degree v := by
          rw [← hconst]
          exact Finset.sum_le_sum fun v _ => hmin v
        have hcard_le : Fintype.card V ≤ 5 := by
          have : 3 * Fintype.card V ≤ 2 * G.edgeFinset.card := by
            rw [← hsumEq]
            exact hlower
          omega
        have hcard : Fintype.card V = 4 ∨ Fintype.card V = 5 := by omega
        rcases hcard with h4 | h5
        · exact unitDistance_of_minDegree_on_four h4 hmin
        · exact unitDistance_of_minDegree_on_five h5 hmin hedge
@[expose] public section
end
end Erdos1007
end

set_option autoImplicit false
@[expose] public section
open Erdos1007
universe u
open SimpleGraph Metric
public section
namespace Erdos1007
theorem _root_.solution
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.edgeFinset.card ≤ 8) :
    ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ u v, G.Adj u v → dist (f u) (f v) = 1 :=
  unitDistance_of_edgeFinset_card_le_eight_aux
    (Fintype.card V + G.edgeFinset.card) le_rfl h
end Erdos1007
