-- Prove2me | solution 1 for BergeMatching.Core.theorem_1_only_if
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T14:59:38.112423+00:00
-- url     : https://prove2.me/submissions/88d87f2d-0dea-4e3c-bbd0-c68fbe9aa029

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace BergeMatching.Core

open SimpleGraph

/-- Edges of `S` pairwise share no vertex. -/
private def EdgeDisj {V : Type} (S : Set (Sym2 V)) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, ∀ x, x ∈ e → x ∈ f → e = f

private lemma edgeDisj_of_isMatching {V : Type} {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : EdgeDisj M.edgeSet := by
  intro e he f hf x hxe hxf
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
  obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hxf
  rw [Subgraph.mem_edgeSet] at he hf
  rw [hM.eq_of_adj_left he hf]

/-- A set of edges of `G` whose edges are pairwise vertex-disjoint is the edge set of a
matching of `G`. -/
private lemma exists_isMatching_of_edgeDisj {V : Type} {G : SimpleGraph V} (S : Set (Sym2 V))
    (hSG : S ⊆ G.edgeSet) (hS : EdgeDisj S) :
    ∃ M' : G.Subgraph, M'.IsMatching ∧ M'.edgeSet = S := by
  let M' : G.Subgraph :=
    { verts := {v | ∃ e ∈ S, v ∈ e},
      Adj := fun u v => s(u, v) ∈ S,
      adj_sub := fun h => hSG h,
      edge_vert := fun {u v} h => ⟨_, h, Sym2.mem_mk_left u v⟩,
      symm := ⟨fun u v h => by simpa [Sym2.eq_swap] using h⟩ }
  refine ⟨M', ?_, ?_⟩
  · rintro v ⟨e, he, hve⟩
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
    refine ⟨w, he, fun w' hw' => ?_⟩
    have := hS _ hw' _ he v (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)
    exact Sym2.congr_right.mp this
  · ext e
    induction e using Sym2.ind with
    | _ u v => rfl

private lemma isChain_alt_diff {V : Type} (N : Set (Sym2 V)) (g : Sym2 V) :
    ∀ l : List (Sym2 V), g ∉ l → l.IsChain (fun e e' => (e ∈ N ↔ e' ∉ N)) →
      l.IsChain (fun e e' => (e ∈ N \ {g} ↔ e' ∉ N \ {g})) := by
  intro l hg hl
  refine hl.imp_of_mem_imp ?_
  intro a b ha hb hab
  have hag : a ≠ g := fun h => hg (h ▸ ha)
  have hbg : b ≠ g := fun h => hg (h ▸ hb)
  simp only [Set.mem_diff, Set.mem_singleton_iff, hag, hbg, not_false_eq_true, and_true]
  exact hab

/-- The core of the augmenting argument: switching a matching `N` along an alternating trail
between two distinct `N`-neutral vertices yields a matching with one more edge, every vertex of
which is either covered by `N` or an endpoint of the trail. -/
private theorem augment {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V} :
    ∀ {u : V} (p : G.Walk u v) (N : Set (Sym2 V)), EdgeDisj N → u ≠ v →
      (∀ e ∈ N, u ∉ e) → (∀ e ∈ N, v ∉ e) → IsAlternatingWrt N p →
      EdgeDisj (symmDiff N {e | e ∈ p.edges}) ∧
        (symmDiff N {e | e ∈ p.edges}).ncard = N.ncard + 1 ∧
        ∀ e ∈ symmDiff N {e | e ∈ p.edges}, ∀ x ∈ e, (∃ f ∈ N, x ∈ f) ∨ x = u ∨ x = v
  | _, .nil, N, _, huv, _, _, _ => absurd rfl huv
  | u, .cons (v := b) hab .nil, N, hN, huv, hu, hv, _ => by
    have habN : s(u, b) ∉ N := fun h => hu _ h (Sym2.mem_mk_left _ _)
    have hT : symmDiff N {e | e ∈ (Walk.cons hab Walk.nil : G.Walk u b).edges} = insert s(u, b) N := by
      ext e
      simp only [Set.mem_symmDiff, Walk.edges_cons, Walk.edges_nil, List.mem_singleton,
        Set.mem_setOf_eq, Set.mem_insert_iff]
      by_cases he : e = s(u, b)
      · subst he; simp [habN]
      · simp [he]
    rw [hT]
    refine ⟨?_, Set.ncard_insert_of_notMem habN, ?_⟩
    · intro e he f hf x hxe hxf
      rcases he with rfl | he <;> rcases hf with rfl | hf
      · rfl
      · rcases Sym2.mem_iff.mp hxe with rfl | rfl
        · exact absurd hxf (hu _ hf)
        · exact absurd hxf (hv _ hf)
      · rcases Sym2.mem_iff.mp hxf with rfl | rfl
        · exact absurd hxe (hu _ he)
        · exact absurd hxe (hv _ he)
      · exact hN _ he _ hf x hxe hxf
    · intro e he x hx
      rcases he with rfl | he
      · rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨e, he, hx⟩
  | u, .cons (v := b) hab (.cons (v := c) hbc r), N, hN, huv, hu, hv, hp => by
    obtain ⟨htr, hch⟩ := hp
    rw [Walk.isTrail_cons, Walk.isTrail_cons] at htr
    obtain ⟨⟨hr, hbc_r⟩, hab_rest⟩ := htr
    simp only [Walk.edges_cons, List.mem_cons, not_or] at hab_rest
    obtain ⟨hab_ne_bc, hab_r⟩ := hab_rest
    simp only [Walk.edges_cons, List.isChain_cons_cons] at hch
    obtain ⟨halt, hch'⟩ := hch
    have habN : s(u, b) ∉ N := fun h => hu _ h (Sym2.mem_mk_left _ _)
    have hbcN : s(b, c) ∈ N := by tauto
    have hrch : r.edges.IsChain (fun e e' => (e ∈ N ↔ e' ∉ N)) := hch'.tail
    set N₁ := N \ {s(b, c)} with hN₁def
    have hN₁ : EdgeDisj N₁ := fun e he f hf => hN e he.1 f hf.1
    -- `c` and `b` are covered in `N` only by `bc`
    have honly : ∀ f ∈ N, ∀ x, x ∈ s(b, c) → x ∈ f → f = s(b, c) :=
      fun f hf x hx hxf => hN f hf _ hbcN x hxf hx
    have hcv : c ≠ v := by
      rintro rfl; exact hv _ hbcN (Sym2.mem_mk_right _ _)
    have hc₁ : ∀ e ∈ N₁, c ∉ e := by
      intro e he hce
      exact he.2 (honly e he.1 c (Sym2.mem_mk_right _ _) hce)
    have hv₁ : ∀ e ∈ N₁, v ∉ e := fun e he => hv e he.1
    have hr_alt : IsAlternatingWrt N₁ r := ⟨hr, isChain_alt_diff N _ r.edges hbc_r hrch⟩
    obtain ⟨hT₁, hcard₁, hcov₁⟩ := augment r N₁ hN₁ hcv hc₁ hv₁ hr_alt
    have hbcT : s(b, c) ∉ r.edges := hbc_r
    -- the switched set is the switched set along `r`, plus the edge `ub`
    have hT : symmDiff N {e | e ∈ (Walk.cons hab (Walk.cons hbc r)).edges} =
        insert s(u, b) (symmDiff N₁ {e | e ∈ r.edges}) := by
      ext e
      simp only [Set.mem_symmDiff, Walk.edges_cons, List.mem_cons, Set.mem_setOf_eq,
        Set.mem_insert_iff, hN₁def, Set.mem_sdiff, Set.mem_singleton_iff]
      by_cases h1 : e = s(u, b)
      · subst h1; simp [habN, hab_r]
      · by_cases h2 : e = s(b, c)
        · subst h2; simp [hbcN, hbc_r, Ne.symm hab_ne_bc]
        · simp [h1, h2]
    have hubT₁ : s(u, b) ∉ symmDiff N₁ {e | e ∈ r.edges} := by
      simp only [Set.mem_symmDiff, Set.mem_setOf_eq, not_or, not_and, not_not]
      exact ⟨fun h => absurd h.1 habN, fun h => absurd h hab_r⟩
    have hbc_ne : b ≠ c := hbc.ne
    have hu_ne_c : u ≠ c := by
      rintro rfl; exact hu _ hbcN (Sym2.mem_mk_right _ _)
    have hb_notcov : ¬ ∃ f ∈ N₁, b ∈ f := by
      rintro ⟨f, hf, hbf⟩
      exact hf.2 (honly f hf.1 b (Sym2.mem_mk_left _ _) hbf)
    have hbv : b ≠ v := by
      rintro rfl; exact hv _ hbcN (Sym2.mem_mk_left _ _)
    have hu_notcov : ¬ ∃ f ∈ N₁, u ∈ f := fun ⟨f, hf, huf⟩ => hu f hf.1 huf
    rw [hT]
    refine ⟨?_, ?_, ?_⟩
    · -- the new edge `ub` is disjoint from the switched set along `r`
      have key : ∀ f ∈ symmDiff N₁ {e | e ∈ r.edges}, ∀ x, x ∈ s(u, b) → x ∉ f := by
        intro f hf x hx hxf
        rcases hcov₁ f hf x hxf with h | rfl | rfl
        · rcases Sym2.mem_iff.mp hx with rfl | rfl
          · exact hu_notcov h
          · exact hb_notcov h
        · rcases Sym2.mem_iff.mp hx with h | h
          · exact hu_ne_c h.symm
          · exact hbc_ne h.symm
        · rcases Sym2.mem_iff.mp hx with h | h
          · exact huv h.symm
          · exact hbv h.symm
      intro e he f hf x hxe hxf
      rcases he with rfl | he <;> rcases hf with rfl | hf
      · rfl
      · exact absurd hxf (key _ hf x hxe)
      · exact absurd hxe (key _ he x hxf)
      · exact hT₁ _ he _ hf x hxe hxf
    · rw [Set.ncard_insert_of_notMem hubT₁, hcard₁, hN₁def, Set.ncard_diff_singleton_add_one hbcN]
    · intro e he x hx
      rcases he with rfl | he
      · rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl ⟨_, hbcN, Sym2.mem_mk_left _ _⟩
      · rcases hcov₁ e he x hx with ⟨f, hf, hxf⟩ | rfl | rfl
        · exact Or.inl ⟨f, hf.1, hxf⟩
        · exact Or.inl ⟨_, hbcN, Sym2.mem_mk_right _ _⟩
        · exact Or.inr (Or.inr rfl)

end BergeMatching.Core

open BergeMatching.Core

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : G.Subgraph) (hM : M.IsMatching) {a a' : V} (p : G.Walk a a')
    (haa' : a ≠ a') (ha : IsNeutral M a) (ha' : IsNeutral M a') (hp : IsAlternatingChain M p) :
    ∃ M' : G.Subgraph, M'.IsMatching ∧
      M'.edgeSet = symmDiff M.edgeSet {e | e ∈ p.edges} ∧
      M.edgeSet.ncard < M'.edgeSet.ncard ∧ ¬ IsMaximumMatching M := by
  obtain ⟨hT, hcard, -⟩ := augment p M.edgeSet (edgeDisj_of_isMatching hM) haa' ha ha' hp
  have hsub : symmDiff M.edgeSet {e | e ∈ p.edges} ⊆ G.edgeSet := by
    intro e he
    rcases he with ⟨he, -⟩ | ⟨he, -⟩
    · exact M.edgeSet_subset he
    · exact p.edges_subset_edgeSet he
  obtain ⟨M', hM', hE⟩ := exists_isMatching_of_edgeDisj _ hsub hT
  refine ⟨M', hM', hE, by rw [hE, hcard]; omega, ?_⟩
  rintro ⟨-, hmax⟩
  have := hmax M' hM'
  rw [hE, hcard] at this
  omega

