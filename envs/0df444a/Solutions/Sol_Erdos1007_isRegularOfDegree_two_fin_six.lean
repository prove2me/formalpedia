-- Prove2me | solution 1 for Erdos1007.isRegularOfDegree_two_fin_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:13.137426+00:00
-- url     : https://prove2.me/submissions/6bbb2216-cf3f-46ee-87d6-123a7db43832

module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sort
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_TwoRegularSix
section
@[expose] public section
namespace Erdos1007
open SimpleGraph
variable {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
private lemma neighborFinset_card_eq_two (h : G.IsRegularOfDegree 2) (v : Fin 6) :
    (G.neighborFinset v).card = 2 := by
  rw [card_neighborFinset_eq_degree, h.degree_eq v]
private lemma neighborFinset_eq_of_adj (h : G.IsRegularOfDegree 2) {v x y : Fin 6}
    (hx : G.Adj v x) (hy : G.Adj v y) (hxy : x ≠ y) : G.neighborFinset v = {x, y} := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro w hw
    rw [mem_neighborFinset] at hw
    by_contra hcon
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
    obtain ⟨hwx, hwy⟩ := hcon
    have h3 : ({w, x, y} : Finset (Fin 6)) ≤ G.neighborFinset v := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact (mem_neighborFinset G v _).mpr hw
      · exact (mem_neighborFinset G v _).mpr hx
      · exact (mem_neighborFinset G v _).mpr hy
    have hw' : w ∉ ({x, y} : Finset (Fin 6)) := by
      simp [hwx, hwy]
    have hxy' : x ∉ ({y} : Finset (Fin 6)) := by
      simp [hxy]
    have h3c : ({w, x, y} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem hw', Finset.card_insert_of_notMem hxy',
        Finset.card_singleton]
    have h4 := Finset.card_le_card h3
    rw [neighborFinset_card_eq_two h v, h3c] at h4
    omega
  · have hxy' : x ∉ ({y} : Finset (Fin 6)) := by
      simp [hxy]
    rw [neighborFinset_card_eq_two h v, Finset.card_insert_of_notMem hxy',
      Finset.card_singleton]
end Erdos1007
end
end

set_option autoImplicit false
@[expose] public section
public section
open Erdos1007
open SimpleGraph
variable {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
set_option maxHeartbeats 1000000
namespace Erdos1007
theorem _root_.solution (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (h : G.IsRegularOfDegree 2) :
    Nonempty (G ≃g SimpleGraph.cycleGraph 6) ∨
      Nonempty (G ≃g (⊤ : SimpleGraph (Fin 3)) ⊕g (⊤ : SimpleGraph (Fin 3))) := by
  -- a vertex other than `u` in the neighbourhood of `v`
  have other : ∀ (v u : Fin 6), G.Adj v u → ∃ w, w ∈ G.neighborFinset v ∧ w ≠ u := by
    intro v u hvu
    obtain ⟨p, q, hp, hq, hpq⟩ := Finset.one_lt_card_iff.mp (by
      rw [neighborFinset_card_eq_two h v]; decide)
    by_cases hpu : p = u
    · exact ⟨q, hq, fun hqu => hpq (hpu.trans hqu.symm)⟩
    · exact ⟨p, hp, hpu⟩
  -- the two neighbours `a` and `b` of vertex `0`
  obtain ⟨a, b, ha, hb, hab⟩ := by
    have h1 : 1 < (G.neighborFinset 0).card := by
      rw [neighborFinset_card_eq_two h 0]; decide
    exact Finset.one_lt_card_iff.mp h1
  have h0a : G.Adj 0 a := (mem_neighborFinset G 0 a).mp ha
  have h0b : G.Adj 0 b := (mem_neighborFinset G 0 b).mp hb
  have ha0 : a ≠ 0 := by
    intro heq; subst heq; exact G.irrefl h0a
  have hb0 : b ≠ 0 := by
    intro heq; subst heq; exact G.irrefl h0b
  have hN0 : G.neighborFinset 0 = {a, b} := neighborFinset_eq_of_adj h h0a h0b hab
  by_cases htri : G.Adj a b
  · -- `0, a, b` form a triangle, and so do the other three vertices
    have hNa : G.neighborFinset a = {0, b} :=
      neighborFinset_eq_of_adj h h0a.symm htri hb0.symm
    have hNb : G.neighborFinset b = {0, a} :=
      neighborFinset_eq_of_adj h h0b.symm htri.symm ha0.symm
    set U : Finset (Fin 6) := {0, a, b} with hUdef
    have hcardU : U.card = 3 := by
      rw [hUdef, Finset.card_insert_of_notMem (by simp [ha0.symm, hb0.symm]),
        Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    -- vertices of `U` have all their neighbours in `U`
    have memU : ∀ ⦃z : Fin 6⦄, z ∈ G.neighborFinset 0 ∨ z ∈ G.neighborFinset a ∨
        z ∈ G.neighborFinset b → z ∈ U := by
      intro z hz
      rw [hUdef]
      rcases hz with hz | hz | hz
      · rw [hN0] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with h | h <;> simp [h]
      · rw [hNa] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with h | h <;> simp [h]
      · rw [hNb] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with h | h <;> simp [h]
    have hUadj : ∀ u v : Fin 6, u ∈ U → v ∈ U → (G.Adj u v ↔ u ≠ v) := by
      intro u v hu hv
      rw [hUdef] at hu hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      obtain rfl | rfl | rfl := hu
      · obtain rfl | rfl | rfl := hv
        · simp
        · simp [h0a, ha0.symm]
        · simp [h0b, hb0.symm]
      · obtain rfl | rfl | rfl := hv
        · simp [h0a.symm, ha0]
        · simp
        · simp [htri, hab]
      · obtain rfl | rfl | rfl := hv
        · simp [h0b.symm, hb0]
        · simp [htri.symm, hab.symm]
        · simp
    have hNv : ∀ v : Fin 6, v ∉ U → G.neighborFinset v = Finset.univ \ (U ∪ {v}) := by
      intro v hv
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro w hw
        rw [mem_neighborFinset] at hw
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, ?_⟩
        intro hwEx
        rcases Finset.mem_union.mp hwEx with hwU | hwv
        · have hvw : v ∈ G.neighborFinset w := (mem_neighborFinset G w v).mpr hw.symm
          rw [hUdef] at hwU
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwU
          rcases hwU with rfl | rfl | rfl
          · exact hv (memU (Or.inl hvw))
          · exact hv (memU (Or.inr (Or.inl hvw)))
          · exact hv (memU (Or.inr (Or.inr hvw)))
        · rw [Finset.mem_singleton] at hwv
          exact G.irrefl (hwv ▸ hw)
      · rw [neighborFinset_card_eq_two h v, Finset.card_sdiff, Finset.card_univ,
          Fintype.card_fin, Finset.inter_univ, Finset.union_singleton,
          Finset.card_insert_of_notMem hv, hcardU]
    have hNoMix : ∀ u v : Fin 6, u ∈ U → v ∉ U → ¬ G.Adj u v := by
      intro u v hu hv huv
      have hmem : u ∈ G.neighborFinset v := (mem_neighborFinset G v u).mpr huv.symm
      rw [hNv v hv] at hmem
      exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_union.mpr (Or.inl hu))
    have hNoMix' : ∀ u v : Fin 6, u ∉ U → v ∈ U → ¬ G.Adj u v := by
      intro u v hu hv huv
      exact hNoMix v u hv hu huv.symm
    have hTout : ∀ u v : Fin 6, u ∉ U → v ∉ U → (G.Adj u v ↔ u ≠ v) := by
      intro u v hu hv
      constructor
      · intro hcon heq
        subst heq
        exact G.irrefl hcon
      · intro hne
        have hmem : u ∈ G.neighborFinset v := by
          rw [hNv v hv]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, by simp [hu, hne]⟩
        exact G.adj_symm ((mem_neighborFinset G v u).mp hmem)
    -- the two halves are each complete, so `G` is two disjoint triangles
    have hcardUc : (Finset.univ \ U).card = 3 := by
      rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, hcardU]
    have eU : Fin 3 ≃ {x : Fin 6 // x ∈ U} := (U.orderIsoOfFin hcardU).toEquiv
    have eT : Fin 3 ≃ {x : Fin 6 // x ∉ U} :=
      ((Finset.univ \ U).orderIsoOfFin hcardUc).toEquiv.trans
        (Equiv.subtypeEquivRight fun x => by simp)
    set e : Fin 6 ≃ Fin 3 ⊕ Fin 3 :=
      (Equiv.sumCompl fun x : Fin 6 => x ∈ U).symm.trans (Equiv.sumCongr eU.symm eT.symm)
      with he
    have hIn : ∀ (u : Fin 6) (hu : u ∈ U), e u = Sum.inl (eU.symm ⟨u, hu⟩) := by
      intro u hu
      simp [he, Equiv.sumCompl_symm_apply_of_pos hu]
    have hOut : ∀ (u : Fin 6) (hu : u ∉ U), e u = Sum.inr (eT.symm ⟨u, hu⟩) := by
      intro u hu
      simp [he, Equiv.sumCompl_symm_apply_of_neg hu]
    refine Or.inr ⟨e, ?_⟩
    intro u v
    by_cases hu : u ∈ U
    · by_cases hv : v ∈ U
      · rw [hIn u hu, hIn v hv, SimpleGraph.sum_adj_inl, SimpleGraph.top_adj]
        refine Iff.trans ?_ (hUadj u v hu hv).symm
        simp [ne_eq]
      · rw [hIn u hu, hOut v hv]
        exact ⟨fun h => absurd h (SimpleGraph.not_adj_sum_inl_inr _ _),
          fun h => absurd h (hNoMix u v hu hv)⟩
    · by_cases hv : v ∈ U
      · rw [hOut u hu, hIn v hv]
        exact ⟨fun h => absurd (adj_symm ((⊤ : SimpleGraph (Fin 3)) ⊕g
          (⊤ : SimpleGraph (Fin 3))) h) (SimpleGraph.not_adj_sum_inl_inr _ _),
          fun h => absurd h (hNoMix' u v hu hv)⟩
      · rw [hOut u hu, hOut v hv, SimpleGraph.sum_adj_inr, SimpleGraph.top_adj]
        refine Iff.trans ?_ (hTout u v hu hv).symm
        simp [ne_eq]
  · -- the neighbours of `0` are not adjacent, so `G` is a hexagon
    -- `c` is the second neighbour of `a`
    obtain ⟨c, hc, hc0⟩ := other a 0 h0a.symm
    have hac : G.Adj a c := (mem_neighborFinset G a c).mp hc
    have hca : G.Adj c a := hac.symm
    have hca' : c ≠ a := by
      intro heq; subst heq; exact G.irrefl hca
    have hcb : c ≠ b := by
      intro heq; subst heq; exact htri hac
    have hNa : G.neighborFinset a = {0, c} :=
      neighborFinset_eq_of_adj h h0a.symm hac hc0.symm
    -- `d` is the second neighbour of `b`
    obtain ⟨d, hd, hd0⟩ := other b 0 h0b.symm
    have hbd : G.Adj b d := (mem_neighborFinset G b d).mp hd
    have hdb : G.Adj d b := hbd.symm
    have hdb' : d ≠ b := by
      intro heq; subst heq; exact G.irrefl hbd
    have hda : d ≠ a := by
      intro heq; subst heq; exact htri hbd.symm
    have hNb : G.neighborFinset b = {0, d} :=
      neighborFinset_eq_of_adj h h0b.symm hbd hd0.symm
    -- `c ≠ d`, or the two vertices left over would be stuck without neighbours
    have hcd : c ≠ d := by
      intro heq
      subst heq
      have hNc : G.neighborFinset c = {a, b} :=
        neighborFinset_eq_of_adj h hca hbd.symm hab
      have hcardS : ({0, a, b, c} : Finset (Fin 6)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [ha0.symm, hb0.symm, hc0.symm]),
          Finset.card_insert_of_notMem (by simp [hab, hca'.symm]),
          Finset.card_insert_of_notMem (by simp [hcb.symm]), Finset.card_singleton]
      have hcard4 : (Finset.univ \ {0, a, b, c}).card = 2 := by
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, hcardS]
      have hrpos : 0 < (Finset.univ \ {0, a, b, c}).card := by rw [hcard4]; decide
      obtain ⟨r, hr⟩ := Finset.card_pos.mp hrpos
      have hr2 : r ∉ ({0, a, b, c} : Finset (Fin 6)) := (Finset.mem_sdiff.mp hr).2
      have hsub : G.neighborFinset r ⊆ Finset.univ \ ({0, a, b, c} ∪ {r}) := by
        intro w hw
        rw [mem_neighborFinset] at hw
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, ?_⟩
        intro hwEx
        rcases Finset.mem_union.mp hwEx with hwU | hwv
        · have hmem : r ∈ G.neighborFinset w := (mem_neighborFinset G w r).mpr hw.symm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwU
          rcases hwU with h | h | h | h
          · rw [h, hN0] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' <;> exact hr2 (by simp [h'])
          · rw [h, hNa] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' <;> exact hr2 (by simp [h'])
          · rw [h, hNb] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' <;> exact hr2 (by simp [h'])
          · rw [h, hNc] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' <;> exact hr2 (by simp [h'])
        · rw [Finset.mem_singleton] at hwv
          exact G.irrefl (hwv ▸ hw)
      have hc1 : (Finset.univ \ ({0, a, b, c} ∪ {r})).card ≤ 1 := by
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
          Finset.union_singleton, Finset.card_insert_of_notMem
            (Finset.mem_sdiff.mp hr).2, hcardS]
      have hc2 : (G.neighborFinset r).card ≤ (Finset.univ \ ({0, a, b, c} ∪ {r})).card :=
        Finset.card_le_card hsub
      rw [neighborFinset_card_eq_two h r] at hc2
      omega
    -- the sixth vertex
    have hcardS5 : ({0, a, b, c, d} : Finset (Fin 6)).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [ha0.symm, hb0.symm, hc0.symm, hd0.symm]),
        Finset.card_insert_of_notMem (by simp [hab, hca'.symm, hda.symm]),
        Finset.card_insert_of_notMem (by simp [hcb.symm, hdb'.symm]),
        Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
    have hcard5 : (Finset.univ \ {0, a, b, c, d}).card = 1 := by
      rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, hcardS5]
    obtain ⟨x, hxset⟩ := Finset.card_eq_one.mp hcard5
    have hxmem : x ∈ Finset.univ \ {0, a, b, c, d} := by rw [hxset]; simp
    have hxmem' : x ∉ ({0, a, b, c, d} : Finset (Fin 6)) := (Finset.mem_sdiff.mp hxmem).2
    have hx0 : x ≠ 0 := by
      intro heq; rw [heq] at hxmem'; exact hxmem' (by simp)
    have hxa : x ≠ a := by
      intro heq; rw [heq] at hxmem'; exact hxmem' (by simp)
    have hxb : x ≠ b := by
      intro heq; rw [heq] at hxmem'; exact hxmem' (by simp)
    have hxc : x ≠ c := by
      intro heq; rw [heq] at hxmem'; exact hxmem' (by simp)
    have hxd : x ≠ d := by
      intro heq; rw [heq] at hxmem'; exact hxmem' (by simp)
    -- `e` is the second neighbour of `c`
    obtain ⟨e, he, hea⟩ := other c a hca
    have hce : G.Adj c e := (mem_neighborFinset G c e).mp he
    have he0 : e ≠ 0 := by
      intro heq
      have hmem : c ∈ ({a, b} : Finset (Fin 6)) := by
        rw [← hN0]
        exact (mem_neighborFinset G 0 c).mpr (by rw [heq] at hce; exact hce.symm)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hca' h
      · exact hcb h
    have heb : e ≠ b := by
      intro heq
      have hmem : c ∈ ({0, d} : Finset (Fin 6)) := by
        rw [← hNb]
        exact (mem_neighborFinset G b c).mpr (by rw [heq] at hce; exact hce.symm)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hc0 h
      · exact hcd h
    have hec : e ≠ c := by
      intro heq; rw [heq] at hce; exact G.irrefl hce
    have hed : e ≠ d := by
      intro heq
      subst heq
      have hNc' : G.neighborFinset c = {a, e} :=
        neighborFinset_eq_of_adj h hca hce hea.symm
      have hNbe : G.neighborFinset e = {b, c} :=
        neighborFinset_eq_of_adj h hdb hce.symm hcb.symm
      have hsub : G.neighborFinset x ⊆ Finset.univ \ ({0, a, b, c, e} ∪ {x}) := by
        intro w hw
        rw [mem_neighborFinset] at hw
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, ?_⟩
        intro hwEx
        rcases Finset.mem_union.mp hwEx with hwU | hwv
        · have hmem : x ∈ G.neighborFinset w := (mem_neighborFinset G w x).mpr hw.symm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwU
          rcases hwU with h | h | h | h | h
          · rw [h, hN0] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' <;> exact hxmem' (by simp [h'])
          · rw [h, hNa] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' <;> exact hxmem' (by simp [h'])
          · rw [h, hNb] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' <;> exact hxmem' (by simp [h'])
          · rw [h, hNc'] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' <;> exact hxmem' (by simp [h'])
          · rw [h, hNbe] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' <;> exact hxmem' (by simp [h'])
        · rw [Finset.mem_singleton] at hwv
          exact G.irrefl (hwv ▸ hw)
      have hc1 : (Finset.univ \ ({0, a, b, c, e} ∪ {x})).card = 0 := by
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
          Finset.union_singleton, Finset.card_insert_of_notMem hxmem', hcardS5]
      have hc2 : (G.neighborFinset x).card ≤ (Finset.univ \ ({0, a, b, c, e} ∪ {x})).card :=
        Finset.card_le_card hsub
      rw [neighborFinset_card_eq_two h x] at hc2
      omega
    -- so `e` is the sixth vertex `x`
    have hex : e ∈ Finset.univ \ {0, a, b, c, d} := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl | rfl | rfl)
      · exact he0 rfl
      · exact hea rfl
      · exact heb rfl
      · exact hec rfl
      · exact hed rfl
    have hex' : e = x := by rw [hxset] at hex; exact Finset.mem_singleton.mp hex
    have hcx : G.Adj c x := by rw [← hex']; exact hce
    have hNc : G.neighborFinset c = {a, x} :=
      neighborFinset_eq_of_adj h hca hcx hxa.symm
    -- `f` is the second neighbour of `d`
    obtain ⟨f, hf, hfb⟩ := other d b hdb
    have hdf : G.Adj d f := (mem_neighborFinset G d f).mp hf
    have hf0 : f ≠ 0 := by
      intro heq
      have hmem : d ∈ ({a, b} : Finset (Fin 6)) := by
        rw [← hN0]
        exact (mem_neighborFinset G 0 d).mpr (by rw [heq] at hdf; exact hdf.symm)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hda h
      · exact hdb' h
    have hfa : f ≠ a := by
      intro heq
      have hmem : d ∈ ({0, c} : Finset (Fin 6)) := by
        rw [← hNa]
        exact (mem_neighborFinset G a d).mpr (by rw [heq] at hdf; exact hdf.symm)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hd0 h
      · exact hcd.symm h
    have hfd : f ≠ d := by
      intro heq; rw [heq] at hdf; exact G.irrefl hdf
    have hfc : f ≠ c := by
      intro heq
      have hmem : d ∈ ({a, x} : Finset (Fin 6)) := by
        rw [← hNc]
        exact (mem_neighborFinset G c d).mpr (by rw [heq] at hdf; exact hdf.symm)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hda h
      · exact hxd h.symm
    -- so `f` is also the sixth vertex
    have hfx : f ∈ Finset.univ \ {0, a, b, c, d} := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ f, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl | rfl | rfl)
      · exact hf0 rfl
      · exact hfa rfl
      · exact hfb rfl
      · exact hfc rfl
      · exact hfd rfl
    have hfx' : f = x := by rw [hxset] at hfx; exact Finset.mem_singleton.mp hfx
    have hdx : G.Adj d x := by rw [← hfx']; exact hdf
    have hNd : G.neighborFinset d = {b, x} :=
      neighborFinset_eq_of_adj h hdb hdx hxb.symm
    have hNx : G.neighborFinset x = {c, d} :=
      neighborFinset_eq_of_adj h (G.adj_symm hcx) (G.adj_symm hdx) hcd
    -- every vertex is one of the six labels
    have huniv : ∀ u : Fin 6, u = 0 ∨ u = a ∨ u = b ∨ u = c ∨ u = d ∨ u = x := by
      intro u
      by_cases hu : u ∈ ({0, a, b, c, d} : Finset (Fin 6))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · have hx' : u ∈ Finset.univ \ {0, a, b, c, d} := by simpa using hu
        rw [hxset] at hx'
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp hx')))))
    -- the adjacency of `G` in terms of the six labels
    have e0 : ∀ w : Fin 6, G.Adj 0 w ↔ (w = a ∨ w = b) := by
      intro w; rw [← mem_neighborFinset, hN0]; simp
    have ea : ∀ w : Fin 6, G.Adj a w ↔ (w = 0 ∨ w = c) := by
      intro w; rw [← mem_neighborFinset, hNa]; simp
    have eb : ∀ w : Fin 6, G.Adj b w ↔ (w = 0 ∨ w = d) := by
      intro w; rw [← mem_neighborFinset, hNb]; simp
    have ec : ∀ w : Fin 6, G.Adj c w ↔ (w = a ∨ w = x) := by
      intro w; rw [← mem_neighborFinset, hNc]; simp
    have ed : ∀ w : Fin 6, G.Adj d w ↔ (w = b ∨ w = x) := by
      intro w; rw [← mem_neighborFinset, hNd]; simp
    have ex : ∀ w : Fin 6, G.Adj x w ↔ (w = c ∨ w = d) := by
      intro w; rw [← mem_neighborFinset, hNx]; simp
    -- the hexagon isomorphism: positions `0, 1, 2, 3, 4, 5` carry `0, a, c, x, d, b`
    have hψiff : ∀ i j : Fin 6, G.Adj (![0, a, c, x, d, b] i) (![0, a, c, x, d, b] j) ↔
        (SimpleGraph.cycleGraph 6).Adj i j := by
      intro i j
      rw [SimpleGraph.cycleGraph_adj]
      have hfalse : ∀ ⦃u v : Fin 6⦄, u ≠ v → (u = v) = False := fun _ _ h =>
        propext (iff_false_intro h)
      fin_cases i <;> fin_cases j <;>
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.reduceFinMk,
          Matrix.cons_val, Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero,
          Fin.reduceEq, zero_sub, false_or, e0, ea, eb, ec, ed, ex, hfalse ha0,
          hfalse ha0.symm, hfalse hb0,
          hfalse hb0.symm, hfalse hab, hfalse hab.symm, hfalse hc0, hfalse hc0.symm,
          hfalse hca', hfalse hca'.symm, hfalse hcb, hfalse hcb.symm, hfalse hd0,
          hfalse hd0.symm, hfalse hda, hfalse hda.symm, hfalse hdb', hfalse hdb'.symm,
          hfalse hcd, hfalse hcd.symm, hfalse hx0, hfalse hx0.symm, hfalse hxa,
          hfalse hxa.symm, hfalse hxb, hfalse hxb.symm, hfalse hxc, hfalse hxc.symm,
          hfalse hxd, hfalse hxd.symm] <;> decide
    have hinj : Function.Injective (![0, a, c, x, d, b] : Fin 6 → Fin 6) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hbij : Function.Bijective (![0, a, c, x, d, b] : Fin 6 → Fin 6) :=
      ⟨hinj, Finite.surjective_of_injective hinj⟩
    refine Or.inl ⟨(Equiv.ofBijective _ hbij).symm, ?_⟩
    intro u v
    obtain ⟨i, rfl⟩ := hbij.2 u
    obtain ⟨j, rfl⟩ := hbij.2 v
    simp only [Equiv.ofBijective_symm_apply_apply]
    exact (hψiff i j).symm
end Erdos1007
