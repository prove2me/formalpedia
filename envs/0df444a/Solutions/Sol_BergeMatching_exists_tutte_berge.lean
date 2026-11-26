-- Prove2me | solution 1 for BergeMatching.exists_tutte_berge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:54:03.795675+00:00
-- url     : https://prove2.me/submissions/39e2209c-68d4-4054-b502-4b4da3255a56

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Theorems.Thm_BergeMatching_two_mul_card_add_le
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
private lemma card_deleteVerts_add [Finite V] (G : SimpleGraph V) (U : Set V) :
    Nat.card ((⊤ : G.Subgraph).deleteVerts U).verts + U.ncard = Nat.card V := by
  have : ((⊤ : G.Subgraph).deleteVerts U).verts = Uᶜ := by ext; simp
  rw [this, Nat.card_coe_set_eq, add_comm, Set.ncard_add_ncard_compl]
private lemma aug_no_tutteViolator [Finite V] (G : SimpleGraph V) (d : ℕ)
    (hd : ∀ U : Set V, oddCount G U ≤ U.ncard + d) (hpar : Even (Nat.card V + d))
    (W : Set (V ⊕ Fin d)) : ¬ (aug G d).IsTutteViolator W := by
  intro hW
  rw [IsTutteViolator] at hW
  by_cases h : ∀ i, Sum.inr i ∈ W
  · have hWeq : W = augSet (Sum.inl ⁻¹' W) d := by
      ext x
      rcases x with a | i
      · simp
      · simp [h i]
    have h1 : oddCount (aug G d) W ≤ W.ncard := by
      rw [hWeq, oddCount_aug_augSet, ncard_augSet]
      exact hd _
    exact absurd hW (not_lt.2 h1)
  · push Not at h
    obtain ⟨i, hi⟩ := h
    set H := ((⊤ : (aug G d).Subgraph).deleteVerts W).coe
    have hj : (Sum.inr i : V ⊕ Fin d) ∈ ((⊤ : (aug G d).Subgraph).deleteVerts W).verts := by
      simpa using hi
    have hconn : ∀ x : ((⊤ : (aug G d).Subgraph).deleteVerts W).verts,
        H.connectedComponentMk x = H.connectedComponentMk ⟨_, hj⟩ := by
      rintro ⟨x, hx⟩
      by_cases hxi : x = Sum.inr i
      · subst hxi; rfl
      · apply ConnectedComponent.connectedComponentMk_eq_of_adj
        have hx' : x ∉ W := by simpa using hx
        simp only [H, Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.verts_top,
          Set.mem_univ, true_and, Subgraph.top_adj]
        refine ⟨hx', hi, ?_⟩
        rcases x with a | i'
        · exact aug_adj_inl_inr
        · refine ⟨hxi, fun _ _ h _ => by cases h⟩
    have hle : H.oddComponents.ncard ≤ 1 := by
      refine (Set.ncard_le_one (Set.toFinite _)).2 fun c _ c' _ => ?_
      induction c using ConnectedComponent.ind
      induction c' using ConnectedComponent.ind
      exact (hconn _).trans (hconn _).symm
    have hW0 : W.ncard = 0 := by
      change W.ncard < H.oddComponents.ncard at hW
      omega
    have hodd : Odd H.oddComponents.ncard := by
      change W.ncard < H.oddComponents.ncard at hW
      have : H.oddComponents.ncard = 1 := by omega
      rw [this]; exact odd_one
    rw [odd_ncard_oddComponents] at hodd
    have := card_deleteVerts_add (aug G d) W
    rw [hW0, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin] at this
    rw [Nat.add_zero] at this
    change Odd (Nat.card ((⊤ : (aug G d).Subgraph).deleteVerts W).verts) at hodd
    rw [this] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) hpar
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
theorem _root_.solution [Finite V] (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      2 * M.edgeSet.ncard + oddCount G U = Nat.card V + U.ncard := by
  classical
  obtain ⟨U0, hU0⟩ := Finite.exists_max (fun U : Set V => (oddCount G U : ℤ) - U.ncard)
  have hge : U0.ncard ≤ oddCount G U0 := by
    have := hU0 ∅
    simp only [Set.ncard_empty, Nat.cast_zero, sub_zero] at this
    omega
  set d := oddCount G U0 - U0.ncard with hd
  have hdU : ∀ U : Set V, oddCount G U ≤ U.ncard + d := by
    intro U
    have := hU0 U
    omega
  have hpar : Even (Nat.card V + d) := by
    have h1 := (odd_ncard_oddComponents (G := ((⊤ : G.Subgraph).deleteVerts U0).coe))
    have h2 := card_deleteVerts_add G U0
    change Odd (oddCount G U0) ↔ _ at h1
    rw [← h2]
    rcases Nat.even_or_odd (oddCount G U0) with he | ho
    · have : Even (Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts) := by
        rw [← Nat.not_odd_iff_even, ← h1, Nat.not_odd_iff_even]; exact he
      have : Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + U0.ncard + d =
          Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + oddCount G U0 := by omega
      rw [this]; exact Even.add (by assumption) he
    · have h3 := h1.1 ho
      have : Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + U0.ncard + d =
          Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + oddCount G U0 := by omega
      rw [this]; exact Odd.add_odd h3 ho
  obtain ⟨M', hM'⟩ := tutte.2 (aug_no_tutteViolator G d hdU hpar)
  let M : G.Subgraph :=
    { verts := {a | ∃ b, M'.Adj (.inl a) (.inl b)}
      Adj a b := M'.Adj (.inl a) (.inl b)
      adj_sub := fun h => aug_adj_inl_inl.1 (M'.adj_sub h)
      edge_vert := fun h => ⟨_, h⟩
      symm := ⟨fun _ _ h => h.symm⟩ }
  have hM : M.IsMatching := by
    rintro a ⟨b, hb⟩
    exact ⟨b, hb, fun c hc => Sum.inl_injective (hM'.1.eq_of_adj_left hc hb)⟩
  have hp : ∀ a : V, ∃ y, M'.Adj (.inl a) y := fun a => (hM'.1 (hM'.2 (.inl a))).exists
  choose p hp using hp
  have hcompl : (M.vertsᶜ).ncard ≤ d := by
    have := Set.ncard_le_ncard_of_injOn (s := M.vertsᶜ)
      (t := Set.range (Sum.inr : Fin d → V ⊕ Fin d)) p ?_ ?_
    · rwa [Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card,
        Fintype.card_fin] at this
    · intro a ha
      rcases hpa : p a with b | i
      · exact absurd ⟨b, hpa ▸ hp a⟩ ha
      · exact ⟨i, rfl⟩
    · intro a _ a' _ h
      have := hM'.1.eq_of_adj_right (hp a) (h ▸ hp a')
      exact Sum.inl_injective this
  have hweak := two_mul_card_add_le hM U0
  have h3 := Set.ncard_add_ncard_compl M.verts
  rw [ncard_verts_eq_two_mul hM] at h3
  exact ⟨M, U0, hM, by omega⟩
end BergeMatching
