-- Prove2me | solution 1 for FlowsNetworks.MultiTerminal.maximal_spanning_subtree_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:46:22.512966+00:00
-- url     : https://prove2.me/submissions/f48b8bca-f3c6-44a6-a60e-e0c4b11f42f8

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree

open FlowsNetworks.MultiTerminal

section g71x
open Classical
variable {V : Type} [Fintype V] [DecidableEq V]

theorem g71x_split (K : SimpleGraph V) (a b : V) {x y : V} (p : K.Walk x y) :
    (K.deleteEdges {s(a, b)}).Reachable x y ∨
      ((K.deleteEdges {s(a, b)}).Reachable x a ∧ (K.deleteEdges {s(a, b)}).Reachable b y) ∨
      ((K.deleteEdges {s(a, b)}).Reachable x b ∧ (K.deleteEdges {s(a, b)}).Reachable a y) := by
  induction p with
  | nil => left; rfl
  | @cons x z y h p ih =>
    by_cases he : s(x, z) = s(a, b)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right; left; exact ⟨SimpleGraph.Reachable.refl _, h1⟩
        · right; left; exact ⟨SimpleGraph.Reachable.refl _, h2⟩
        · left; exact h2
      · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right; right; exact ⟨SimpleGraph.Reachable.refl _, h1⟩
        · left; exact h2
        · right; right; exact ⟨SimpleGraph.Reachable.refl _, h2⟩
    · have hadj : (K.deleteEdges {s(a, b)}).Adj x z := by
        rw [SimpleGraph.deleteEdges_adj]; exact ⟨h, by simpa using he⟩
      have hr := hadj.reachable
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact hr.trans h1
      · right; left; exact ⟨hr.trans h1, h2⟩
      · right; right; exact ⟨hr.trans h1, h2⟩

theorem g71x_reach_of_adj {H K : SimpleGraph V} (h : ∀ x y, H.Adj x y → K.Reachable x y)
    {x y : V} (p : H.Walk x y) : K.Reachable x y := by
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- exchange: T tree, e = s(a,b) an edge, u v not joined in T - e; then T - e + uv is a tree -/
theorem g71x_exch_tree (T : SimpleGraph V) (hT : T.IsTree) (a b u v : V) (hab : T.Adj a b)
    (hnr : ¬ (T.deleteEdges {s(a, b)}).Reachable u v) :
    ((T.deleteEdges {s(a, b)}) ⊔ SimpleGraph.edge u v).IsTree := by
  set H := T.deleteEdges {s(a, b)} with hH
  set T'' := H ⊔ SimpleGraph.edge u v with hT''
  have huv : u ≠ v := fun h => hnr (h ▸ SimpleGraph.Reachable.refl _)
  have hHle : H ≤ T'' := le_sup_left
  have hHr : ∀ {x y}, H.Reachable x y → T''.Reachable x y := fun h => h.mono hHle
  have hnew : T''.Adj u v := by
    rw [hT'', SimpleGraph.sup_adj]; right
    rw [SimpleGraph.edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
  have hab' : T''.Reachable a b := by
    have hu := g71x_split T a b (hT.connected.preconnected u a).some
    have hv := g71x_split T a b (hT.connected.preconnected v a).some
    rw [← hH] at hu hv
    -- reduce to: u reaches a or b in H, v reaches a or b in H
    have hu' : H.Reachable u a ∨ H.Reachable u b := by
      rcases hu with h | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr h
    have hv' : H.Reachable v a ∨ H.Reachable v b := by
      rcases hv with h | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr h
    rcases hu' with h1 | h1 <;> rcases hv' with h2 | h2
    · exact absurd (h1.trans h2.symm) hnr
    · exact ((hHr h1).symm.trans hnew.reachable).trans (hHr h2)
    · exact (((hHr h2).symm.trans hnew.reachable.symm).trans (hHr h1)).symm.symm
    · exact absurd (h1.trans h2.symm) hnr
  refine ⟨?_, ?_⟩
  · have : Nonempty V := ⟨u⟩
    rw [SimpleGraph.connected_iff]
    refine ⟨fun x y => g71x_reach_of_adj (H := T) ?_ (hT.connected.preconnected x y).some,
      inferInstance⟩
    intro x y hxy
    by_cases he : s(x, y) = s(a, b)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab'
      · exact hab'.symm
    · apply SimpleGraph.Adj.reachable
      rw [hT'', SimpleGraph.sup_adj]; left
      rw [hH, SimpleGraph.deleteEdges_adj]; exact ⟨hxy, by simpa using he⟩
  · exact SimpleGraph.IsAcyclic.sup_edge_of_not_reachable hnr
      (hT.isAcyclic.anti (SimpleGraph.deleteEdges_le _))


theorem g71x_exch_edges (T : SimpleGraph V) (a b u v : V)
    (hnr : ¬ (T.deleteEdges {s(a, b)}).Reachable u v) (H : SimpleGraph V)
    (hH : H = (T.deleteEdges {s(a, b)}) ⊔ SimpleGraph.edge u v) :
    Finset.univ.filter (fun e => e ∈ H.edgeSet)
      = insert s(u, v) ((Finset.univ.filter (fun e => e ∈ T.edgeSet)).erase s(a, b)) := by
  have huv : u ≠ v := fun h => hnr (h ▸ SimpleGraph.Reachable.refl _)
  subst hH
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase,
    SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges, SimpleGraph.edgeSet_edge_of_ne huv,
    Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
  tauto


theorem g71x_exch_notmem (T : SimpleGraph V) (a b u v : V)
    (hnr : ¬ (T.deleteEdges {s(a, b)}).Reachable u v) :
    s(u, v) ∉ (Finset.univ.filter (fun e => e ∈ T.edgeSet)).erase s(a, b) := by
  intro h
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at h
  apply hnr
  apply SimpleGraph.Adj.reachable
  rw [SimpleGraph.deleteEdges_adj]
  exact ⟨h.2, by simpa using h.1⟩

theorem g71x_length_eq (c : Sym2 V → ℝ) (H : SimpleGraph V) :
    length c H = ∑ e ∈ Finset.univ.filter (fun e => e ∈ H.edgeSet), c e := by
  unfold length
  congr 1

theorem g71x_exch_length (T : SimpleGraph V) (c : Sym2 V → ℝ) (a b u v : V) (hab : T.Adj a b)
    (hnr : ¬ (T.deleteEdges {s(a, b)}).Reachable u v) :
    length c ((T.deleteEdges {s(a, b)}) ⊔ SimpleGraph.edge u v) = length c T - c s(a, b) + c s(u, v) := by

  rw [g71x_length_eq, g71x_length_eq, g71x_exch_edges T a b u v hnr _ rfl, Finset.sum_insert (g71x_exch_notmem T a b u v hnr),
    Finset.sum_erase_eq_sub (by simpa using hab)]
  ring

theorem g71x_le (G T : SimpleGraph V) (hTG : T ≤ G) (a b u v : V) (huv : G.Adj u v) :
    (T.deleteEdges {s(a, b)}) ⊔ SimpleGraph.edge u v ≤ G :=
  sup_le ((SimpleGraph.deleteEdges_le _).trans hTG) ((SimpleGraph.edge_le_iff G).2 (Or.inr huv))

noncomputable def g71x_E (H : SimpleGraph V) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => e ∈ H.edgeSet)

theorem g71x_mem_E (H : SimpleGraph V) (e : Sym2 V) : e ∈ g71x_E H ↔ e ∈ H.edgeSet := by
  unfold g71x_E; simp

theorem g71x_card_E (H : SimpleGraph V) (hH : H.IsTree) : (g71x_E H).card + 1 = Fintype.card V := by
  have h := (SimpleGraph.isTree_iff_connected_and_card.1 hH).2
  have : Nat.card H.edgeSet = (g71x_E H).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun e => (g71x_mem_E H e).symm))
  rw [this, Nat.card_eq_fintype_card] at h
  exact h

theorem g71x_step (G T : SimpleGraph V) (a : Sym2 V → ℝ) (hT : IsSpanningSubtree G T)
    (hcond : OutOfTreeCondition G T a) (T' : SimpleGraph V) (hT' : IsSpanningSubtree G T')
    (x y : V) (hxy : T'.Adj x y) (hnT : ¬ T.Adj x y) :
    ∃ T'', IsSpanningSubtree G T'' ∧ length a T' ≤ length a T'' ∧
      (g71x_E T'' \ g71x_E T).card < (g71x_E T' \ g71x_E T).card := by
  have hGxy : G.Adj x y := hT'.1 hxy
  set P := (hT.2.connected.preconnected x y).some.toPath with hP
  set H' := T'.deleteEdges {s(x, y)} with hH'
  have hbr : ¬ H'.Reachable x y := by
    have := SimpleGraph.isAcyclic_iff_forall_isBridge.1 hT'.2.isAcyclic
      ((SimpleGraph.mem_edgeSet T').2 hxy)
    rwa [SimpleGraph.isBridge_iff] at this
  obtain ⟨d, hd, hd1, hd2⟩ := P.val.exists_boundary_dart {w | H'.Reachable x w}
    (SimpleGraph.Reachable.refl _) hbr
  have hd1' : H'.Reachable x d.fst := hd1
  have hd2' : ¬ H'.Reachable x d.snd := hd2
  have huvT : T.Adj d.fst d.snd := d.adj
  have hnr : ¬ H'.Reachable d.fst d.snd := fun h => hd2' (hd1'.trans h)
  refine ⟨(T'.deleteEdges {s(x, y)}) ⊔ SimpleGraph.edge d.fst d.snd,
    ⟨g71x_le G T' hT'.1 x y d.fst d.snd (hT.1 huvT),
     g71x_exch_tree T' hT'.2 x y d.fst d.snd hxy hnr⟩, ?_, ?_⟩
  · rw [g71x_exch_length T' a x y d.fst d.snd hxy hnr]
    have hmem : d.edge ∈ P.val.edges := by
      unfold SimpleGraph.Walk.edges; exact List.mem_map_of_mem hd
    have := hcond x y hGxy hnT P.val P.prop d.edge hmem
    have he : d.edge = s(d.fst, d.snd) := rfl
    rw [he] at this
    linarith
  · have hE : g71x_E ((T'.deleteEdges {s(x, y)}) ⊔ SimpleGraph.edge d.fst d.snd)
        = insert s(d.fst, d.snd) ((g71x_E T').erase s(x, y)) :=
      g71x_exch_edges T' x y d.fst d.snd hnr _ rfl
    have h1 : s(d.fst, d.snd) ∈ g71x_E T := (g71x_mem_E _ _).2 huvT
    have h2 : s(x, y) ∉ g71x_E T := fun h => hnT ((g71x_mem_E _ _).1 h)
    have h3 : s(x, y) ∈ g71x_E T' := (g71x_mem_E _ _).2 hxy
    have hsd : g71x_E ((T'.deleteEdges {s(x, y)}) ⊔ SimpleGraph.edge d.fst d.snd) \ g71x_E T
        = (g71x_E T' \ g71x_E T).erase s(x, y) := by
      rw [hE]
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨h | ⟨hne, hm⟩, hnot⟩
        · exact absurd (h ▸ h1) hnot
        · exact ⟨hne, hm, hnot⟩
      · rintro ⟨hne, hm, hnot⟩
        exact ⟨Or.inr ⟨hne, hm⟩, hnot⟩
    rw [hsd]
    exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.2 ⟨h3, h2⟩)

end g71x

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G T : SimpleGraph N) (hG : G.Connected) (a : Sym2 N → ℝ)
    (hT : IsSpanningSubtree G T) :
    IsMaximalSpanningSubtree G T a ↔ OutOfTreeCondition G T a := by
  constructor
  · rintro ⟨-, hmax⟩ x y hxy hnT p hp e he
    have heT : e ∈ T.edgeSet := p.edges_subset_edgeSet he
    induction e using Sym2.ind with
    | h c d =>
    have hcd : T.Adj c d := heT
    have hnr : ¬ (T.deleteEdges {s(c, d)}).Reachable x y := by
      rintro ⟨q⟩
      set q' := q.toPath
      have hq'e : s(c, d) ∉ (q'.val).edges := by
        intro hm
        have := (q'.val).edges_subset_edgeSet hm
        rw [SimpleGraph.edgeSet_deleteEdges] at this
        exact this.2 rfl
      have hpath : ((q'.val).mapLe (SimpleGraph.deleteEdges_le _)).IsPath :=
        (SimpleGraph.Walk.isPath_mapLe _).2 q'.prop
      have heq := hT.2.isAcyclic.path_unique ⟨p, hp⟩ ⟨_, hpath⟩
      have : p = (q'.val).mapLe (SimpleGraph.deleteEdges_le _) := congrArg Subtype.val heq
      rw [this, SimpleGraph.Walk.edges_mapLe_eq_edges] at he
      exact hq'e he
    have := hmax _ ⟨g71x_le G T hT.1 c d x y hxy, g71x_exch_tree T hT.2 c d x y hcd hnr⟩
    rw [g71x_exch_length T a c d x y hcd hnr] at this
    linarith
  · intro hcond
    refine ⟨hT, ?_⟩
    suffices H : ∀ k, ∀ T', IsSpanningSubtree G T' → (g71x_E T' \ g71x_E T).card = k →
        length a T' ≤ length a T from fun T' hT' => H _ T' hT' rfl
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro T' hT' hk
    by_cases hemp : g71x_E T' \ g71x_E T = ∅
    · have hsub : g71x_E T' ⊆ g71x_E T := Finset.sdiff_eq_empty_iff_subset.1 hemp
      have hc1 := g71x_card_E T' hT'.2
      have hc2 := g71x_card_E T hT.2
      have heq : g71x_E T' = g71x_E T := Finset.eq_of_subset_of_card_le hsub (by omega)
      have : T' = T := by
        rw [← SimpleGraph.edgeSet_inj]
        ext e
        rw [← g71x_mem_E, ← g71x_mem_E, heq]
      rw [this]
    · obtain ⟨e', he'⟩ := Finset.nonempty_iff_ne_empty.2 hemp
      rw [Finset.mem_sdiff, g71x_mem_E, g71x_mem_E] at he'
      induction e' using Sym2.ind with
      | h x y =>
      obtain ⟨T'', hT'', hlen, hlt⟩ := g71x_step G T a hT hcond T' hT' x y he'.1 he'.2
      have := ih _ (hk ▸ hlt) T'' hT'' rfl
      linarith
