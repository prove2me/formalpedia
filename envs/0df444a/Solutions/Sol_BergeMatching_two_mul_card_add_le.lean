-- Prove2me | solution 1 for BergeMatching.two_mul_card_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:53:12.450505+00:00
-- url     : https://prove2.me/submissions/ceed287d-6134-40d4-a613-095defde3845

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
section
@[expose] public section
open SimpleGraph
namespace BergeMatching
variable {V : Type*}
private lemma ncard_oddComponents_congr {W W' : Type*} {H : SimpleGraph W} {H' : SimpleGraph W'}
    (e : H ≃g H') : H.oddComponents.ncard = H'.oddComponents.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  refine Nat.card_congr (e.connectedComponentEquiv.subtypeEquiv fun c => ?_)
  simp only [Set.mem_ofPred_eq]
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr (ConnectedComponent.isoEquivSupp e c)]
open Finset in
private lemma ncard_verts_eq_two_mul [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  have h := M.spanningCoe.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
    intro v
    rw [Subgraph.degree_spanningCoe]
    split_ifs with hv
    · exact (Subgraph.isMatching_iff_forall_degree.1 hM) v hv
    · exact Subgraph.degree_of_notMem_verts hv
  simp only [hdeg, Finset.sum_boole, Nat.cast_id] at h
  have e1 : M.verts.ncard = #{x | x ∈ M.verts} := by
    rw [← Set.ncard_coe_finset]; congr; ext; simp
  have e2 : M.edgeSet.ncard = #M.spanningCoe.edgeFinset := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset, Subgraph.edgeSet_spanningCoe]
  rw [e1, e2, h]
@[simp] private lemma aug_adj_inl_inr {G : SimpleGraph V} {d : ℕ} {a : V} {i : Fin d} :
    (aug G d).Adj (.inl a) (.inr i) :=
  show _ ∧ _ from ⟨Sum.inl_ne_inr, fun _ _ _ h => by cases h⟩
@[simp] private lemma aug_adj_inr_inl {G : SimpleGraph V} {d : ℕ} {a : V} {i : Fin d} :
    (aug G d).Adj (.inr i) (.inl a) :=
  aug_adj_inl_inr.symm
@[simp] private lemma inl_mem_augSet {U : Set V} {d : ℕ} {a : V} :
    (Sum.inl a : V ⊕ Fin d) ∈ augSet U d ↔ a ∈ U := by
  simp [augSet]
@[simp] private lemma inr_mem_augSet {U : Set V} {d : ℕ} {i : Fin d} :
    (Sum.inr i : V ⊕ Fin d) ∈ augSet U d := by
  simp [augSet]
private lemma ncard_augSet [Finite V] (U : Set V) (d : ℕ) : (augSet U d).ncard = U.ncard + d := by
  rw [augSet, Set.ncard_union_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Set.disjoint_left]
  rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
  cases hi
private lemma oddCount_aug_augSet [Finite V] (G : SimpleGraph V) (U : Set V) (d : ℕ) :
    oddCount (aug G d) (augSet U d) = oddCount G U := by
  let f : ((⊤ : G.Subgraph).deleteVerts U).verts →
      ((⊤ : (aug G d).Subgraph).deleteVerts (augSet U d)).verts :=
    fun a => ⟨Sum.inl a.1, by
      have := a.2
      simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
        true_and, augSet, Set.mem_union, Set.mem_image, Sum.inl.injEq, exists_eq_right,
        Set.mem_range, reduceCtorEq, exists_false, or_false] at this ⊢
      exact this⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (Sum.inl_injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨x, hx⟩
    simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
      true_and, augSet, Set.mem_union, Set.mem_image, Set.mem_range, not_or] at hx
    rcases x with a | i
    · refine ⟨⟨a, ?_⟩, rfl⟩
      simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
        true_and]
      exact fun ha => hx.1 ⟨a, ha, rfl⟩
    · exact absurd ⟨i, rfl⟩ hx.2
  let e : ((⊤ : G.Subgraph).deleteVerts U).coe ≃g
      ((⊤ : (aug G d).Subgraph).deleteVerts (augSet U d)).coe :=
    { Equiv.ofBijective f hf with
      map_rel_iff' := by
        intro a b
        simp [f, inl_mem_augSet] }
  exact (ncard_oddComponents_congr e).symm
private lemma liftSub_isMatching {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching) (d : ℕ) :
    (liftSub M d).IsMatching := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hu⟩ := hM ha
  refine ⟨.inl b, ⟨a, b, rfl, rfl, hb⟩, ?_⟩
  rintro _ ⟨a', b', h1, rfl, h⟩
  cases h1
  rw [hu b' h]
section BergeHelpers
variable {G : SimpleGraph V}
end BergeHelpers
end BergeMatching
end
end

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeMatching
variable {V : Type*}
namespace BergeMatching
theorem _root_.solution [Finite V] {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching)
    (U : Set V) : 2 * M.edgeSet.ncard + oddCount G U ≤ Nat.card V + U.ncard := by
  classical
  set d := (M.vertsᶜ).ncard with hd
  let s : Set (V ⊕ Fin d) := Sum.inl '' M.vertsᶜ
  let t : Set (V ⊕ Fin d) := Set.range Sum.inr
  have hst : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
    cases hi
  have hcard : Nat.card s = Nat.card t := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
      Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨f⟩ := Finite.card_eq.1 hcard
  have hadj : ∀ v : s, (aug G d).Adj v (f v) := by
    rintro ⟨_, a, _, rfl⟩
    generalize f _ = y
    obtain ⟨_, i, rfl⟩ := y
    exact aug_adj_inl_inr
  obtain ⟨M2, hM2v, hM2⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hst f hadj
  have hM1 := liftSub_isMatching hM d
  have hdisj : Disjoint (liftSub M d).support M2.support := by
    rw [hM1.support_eq_verts, hM2.support_eq_verts, hM2v, Set.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      cases hab
      exact hb ha
    · rw [Set.disjoint_left]
      rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
      cases hi
  have hperf : (liftSub M d ⊔ M2).IsPerfectMatching := by
    refine ⟨hM1.sup hM2 hdisj, fun x => ?_⟩
    rw [Subgraph.verts_sup, hM2v]
    rcases x with a | i
    · by_cases ha : a ∈ M.verts
      · exact Or.inl ⟨a, ha, rfl⟩
      · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
  have h1 := not_isTutteViolator_of_isPerfectMatching hperf (augSet U d)
  rw [IsTutteViolator, not_lt] at h1
  have h2 : oddCount (aug G d) (augSet U d) ≤ U.ncard + d := by
    rw [← ncard_augSet]; exact h1
  rw [oddCount_aug_augSet] at h2
  have h3 := Set.ncard_add_ncard_compl M.verts
  rw [ncard_verts_eq_two_mul hM] at h3
  omega
end BergeMatching
