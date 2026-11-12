-- Prove2me | solution 1 for BunkbedFalse.hollom_alt_probs
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T22:38:53.185416+00:00
-- url     : https://prove2.me/submissions/3b956bd5-9693-4cfd-aa58-f40657982b0d

import Definitions.Def_BunkbedHypergraph

/-!
# Lemma 3.1 of Gladkov-Pak-Zimin

`Palt[u1 <-> u10] = 12/64` and `Palt[u1 <-> u10-prime] = 13/64` for Hollom's 3-uniform
hypergraph.

The sum over the 64 level assignments is expanded into 64 explicit terms, so that the rational
arithmetic is done by `norm_num` at elaboration time and never has to reduce inside the kernel.
Each configuration is then settled by an explicit **certificate** rather than by search:

* 48 of the 64 assignments die structurally (`notreach`): `u1` belongs to only one hyperedge and
  `u10` to only one, and neither belongs to `T`, so neither carries a post; hence the relevant
  endpoint has no incident edge whatsoever unless its hyperedge sits on the right level.
* each of the 25 surviving connected assignments is witnessed by an explicit walk (`hop`);
* each of the 7 surviving disconnected assignments is witnessed by an explicit
  adjacency-closed vertex set containing `(u1,0)` but not the target (`not_reach`).

Every `decide` in this file is applied to the elementary adjacency criterion of
`altBB_adj_iff` -- no `Sym2`, no images, no deduplicating unions, and no `DecidableRel`
instance for `Adj` is ever required. In particular no `decide` here searches a graph.
-/

open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace L31

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-! ## An elementary description of adjacency -/

lemma mem_cliqueAt {V : Type*} [Fintype V] [DecidableEq V] (s : Finset V) (l : Fin 2)
    (u v : V × Fin 2) :
    s(u, v) ∈ cliqueAt s l ↔ u.1 ∈ s ∧ v.1 ∈ s ∧ u.1 ≠ v.1 ∧ u.2 = l ∧ v.2 = l := by
  simp only [cliqueAt, mem_image, mem_filter, mem_product, Sym2.eq_iff, Prod.exists]
  aesop

lemma mem_posts {V : Type*} [Fintype V] [DecidableEq V] (T : Finset V) (u v : V × Fin 2) :
    s(u, v) ∈ posts T ↔ u.1 = v.1 ∧ u.1 ∈ T ∧ u.2 ≠ v.2 := by
  obtain ⟨a, i⟩ := u; obtain ⟨b, j⟩ := v
  simp only [posts, mem_image, Sym2.eq_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, (⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ | ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩)⟩ <;> simp_all
  · rintro ⟨rfl, hT, hij⟩
    exact ⟨a, hT, by fin_cases i <;> fin_cases j <;> simp_all⟩

/-- `u ¬ v` iff some hyperedge placed on their common level contains both, or they are the two
ends of a post. -/
lemma altBB_adj_iff {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]
    (e : ι → Finset V) (T : Finset V) (σ : ι → Fin 2) (u v : V × Fin 2) :
    (altBBGraph e T σ).Adj u v ↔
      ((u.1 ≠ v.1 ∧ u.2 = v.2 ∧ ∃ i, u.2 = σ i ∧ u.1 ∈ e i ∧ v.1 ∈ e i)
        ∨ (u.1 = v.1 ∧ u.1 ∈ T ∧ u.2 ≠ v.2)) := by
  rw [altBBGraph, ofEdges, fromEdgeSet_adj]
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, mem_union, mem_biUnion,
    Finset.mem_univ, true_and, mem_cliqueAt, mem_posts]
  constructor
  · rintro ⟨h | h, hne⟩
    · obtain ⟨i, hu, hv, huv, hu2, hv2⟩ := h
      exact Or.inl ⟨huv, by rw [hu2, hv2], i, hu2, hu, hv⟩
    · exact Or.inr h
  · rintro (⟨huv, h2, i, hi, hu, hv⟩ | ⟨h1, hT, h2⟩)
    · refine ⟨Or.inl ⟨i, hu, hv, huv, hi, by rw [← h2]; exact hi⟩, ?_⟩
      exact fun h => huv (by rw [h])
    · refine ⟨Or.inr ⟨h1, hT, h2⟩, ?_⟩
      exact fun h => h2 (by rw [h])

/-! ## Certificates -/

/-- Prepend one edge to a walk, with the adjacency given by the elementary criterion. -/
private lemma hop {σ : Fin 6 → Fin 2} {a b c : Fin 10 × Fin 2}
    (h : (a.1 ≠ b.1 ∧ a.2 = b.2 ∧ ∃ i, a.2 = σ i ∧ a.1 ∈ hollomE i ∧ b.1 ∈ hollomE i)
        ∨ (a.1 = b.1 ∧ a.1 ∈ hollomT ∧ a.2 ≠ b.2))
    (r : (altBBGraph hollomE hollomT σ).Reachable b c) :
    (altBBGraph hollomE hollomT σ).Reachable a c :=
  (((altBB_adj_iff hollomE hollomT σ a b).mpr h).reachable).trans r

private lemma walk_closed {V : Type*} {G : SimpleGraph V} {S : V → Prop}
    (hcl : ∀ x y, S x → G.Adj x y → S y) : ∀ {x y : V}, G.Walk x y → S x → S y := by
  intro x y w
  induction w with
  | nil => exact id
  | cons h p ih => exact fun hx => ih (hcl _ _ hx h)

/-- A set closed under adjacency, containing `u` but not `v`, separates them. The closure
hypothesis is stated via the elementary criterion so that it is cheap to decide. -/
private lemma not_reach (σ : Fin 6 → Fin 2) (S : Fin 10 × Fin 2 → Prop)
    {u v : Fin 10 × Fin 2}
    (hcl : ∀ x y : Fin 10 × Fin 2, S x →
      ((x.1 ≠ y.1 ∧ x.2 = y.2 ∧ ∃ i, x.2 = σ i ∧ x.1 ∈ hollomE i ∧ y.1 ∈ hollomE i)
        ∨ (x.1 = y.1 ∧ x.1 ∈ hollomT ∧ x.2 ≠ y.2)) → S y)
    (hu : S u) (hv : ¬ S v) :
    ¬ (altBBGraph hollomE hollomT σ).Reachable u v := by
  intro hr
  obtain ⟨w⟩ := hr
  exact hv (walk_closed
    (fun x y hx hadj => hcl x y hx ((altBB_adj_iff hollomE hollomT σ x y).mp hadj)) w hu)

/-! ## Isolation kills 48 of the 64 assignments -/

private lemma eq_of_isolated {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : ∀ w, ¬ G.Adj u w) (hr : G.Reachable u v) : v = u := by
  obtain ⟨p⟩ := hr
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (h _)

private lemma zero_isolated (σ : Fin 6 → Fin 2) (h : σ 0 = 1) (w : Fin 10 × Fin 2) :
    ¬ (altBBGraph hollomE hollomT σ).Adj ((0 : Fin 10), (0 : Fin 2)) w := by
  have hE : ∀ j : Fin 6, (0 : Fin 10) ∈ hollomE j → j = 0 := by decide
  rw [altBB_adj_iff]
  rintro (⟨-, -, i, hi, hu, -⟩ | ⟨-, hT, -⟩)
  · have hi0 : i = 0 := hE i hu
    subst hi0
    rw [h] at hi
    exact absurd hi (by decide)
  · exact absurd hT (by decide)

private lemma nine_isolated (σ : Fin 6 → Fin 2) (l : Fin 2) (h : σ 5 ≠ l) (w : Fin 10 × Fin 2) :
    ¬ (altBBGraph hollomE hollomT σ).Adj ((9 : Fin 10), l) w := by
  have hE : ∀ j : Fin 6, (9 : Fin 10) ∈ hollomE j → j = 5 := by decide
  rw [altBB_adj_iff]
  rintro (⟨-, -, i, hi, hu, -⟩ | ⟨-, hT, -⟩)
  · have hi5 : i = 5 := hE i hu
    subst hi5
    exact h hi.symm
  · exact absurd hT (show (9 : Fin 10) ∉ hollomT by decide)

/-- If `u1`'s hyperedge is upstairs, or `u10`'s hyperedge is not on level `l`, the relevant
endpoint is isolated and the two cannot be connected. -/
private lemma notreach (σ : Fin 6 → Fin 2) (l : Fin 2) (h : σ 0 = 1 ∨ σ 5 ≠ l) :
    ¬ (altBBGraph hollomE hollomT σ).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), l) := by
  intro hr
  rcases h with h | h
  · exact absurd (congrArg Prod.fst (eq_of_isolated (zero_isolated σ h) hr))
      (show ¬ (9 : Fin 10) = 0 by decide)
  · exact absurd (congrArg Prod.fst (eq_of_isolated (nine_isolated σ l h) hr.symm))
      (show ¬ (0 : Fin 10) = 9 by decide)

/-! ## The 64 assignments, for each of the two targets -/

-- target (u10, 0)
private lemma c0_000000 : (altBBGraph hollomE hollomT ![0,0,0,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_000001 : ¬ (altBBGraph hollomE hollomT ![0,0,0,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_000010 : (altBBGraph hollomE hollomT ![0,0,0,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_000011 : ¬ (altBBGraph hollomE hollomT ![0,0,0,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_000100 : (altBBGraph hollomE hollomT ![0,0,0,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_000101 : ¬ (altBBGraph hollomE hollomT ![0,0,0,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_000110 : (altBBGraph hollomE hollomT ![0,0,0,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_000111 : ¬ (altBBGraph hollomE hollomT ![0,0,0,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_001000 : (altBBGraph hollomE hollomT ![0,0,1,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_001001 : ¬ (altBBGraph hollomE hollomT ![0,0,1,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_001010 : (altBBGraph hollomE hollomT ![0,0,1,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_001011 : ¬ (altBBGraph hollomE hollomT ![0,0,1,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_001100 : (altBBGraph hollomE hollomT ![0,0,1,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_001101 : ¬ (altBBGraph hollomE hollomT ![0,0,1,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_001110 : (altBBGraph hollomE hollomT ![0,0,1,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_001111 : ¬ (altBBGraph hollomE hollomT ![0,0,1,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_010000 : (altBBGraph hollomE hollomT ![0,1,0,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((1 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((3 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((7 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_010001 : ¬ (altBBGraph hollomE hollomT ![0,1,0,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_010010 : ¬ (altBBGraph hollomE hollomT ![0,1,0,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  not_reach _ (fun z => z ∈ [((0 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (1 : Fin 2)), ((2 : Fin 10), (0 : Fin 2)), ((3 : Fin 10), (0 : Fin 2)), ((3 : Fin 10), (1 : Fin 2)), ((4 : Fin 10), (0 : Fin 2)), ((5 : Fin 10), (0 : Fin 2)), ((6 : Fin 10), (0 : Fin 2)), ((6 : Fin 10), (1 : Fin 2)), ((7 : Fin 10), (1 : Fin 2))]) (by decide) (by decide) (by decide)
private lemma c0_010011 : ¬ (altBBGraph hollomE hollomT ![0,1,0,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_010100 : ¬ (altBBGraph hollomE hollomT ![0,1,0,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  not_reach _ (fun z => z ∈ [((0 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (1 : Fin 2)), ((2 : Fin 10), (0 : Fin 2)), ((3 : Fin 10), (1 : Fin 2)), ((4 : Fin 10), (1 : Fin 2))]) (by decide) (by decide) (by decide)
private lemma c0_010101 : ¬ (altBBGraph hollomE hollomT ![0,1,0,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_010110 : ¬ (altBBGraph hollomE hollomT ![0,1,0,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  not_reach _ (fun z => z ∈ [((0 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (1 : Fin 2)), ((2 : Fin 10), (0 : Fin 2)), ((3 : Fin 10), (1 : Fin 2)), ((4 : Fin 10), (0 : Fin 2)), ((4 : Fin 10), (1 : Fin 2)), ((5 : Fin 10), (0 : Fin 2)), ((6 : Fin 10), (0 : Fin 2)), ((6 : Fin 10), (1 : Fin 2)), ((7 : Fin 10), (1 : Fin 2))]) (by decide) (by decide) (by decide)
private lemma c0_010111 : ¬ (altBBGraph hollomE hollomT ![0,1,0,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_011000 : (altBBGraph hollomE hollomT ![0,1,1,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((1 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((3 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((7 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_011001 : ¬ (altBBGraph hollomE hollomT ![0,1,1,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_011010 : ¬ (altBBGraph hollomE hollomT ![0,1,1,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  not_reach _ (fun z => z ∈ [((0 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (1 : Fin 2)), ((2 : Fin 10), (0 : Fin 2)), ((3 : Fin 10), (0 : Fin 2)), ((4 : Fin 10), (0 : Fin 2))]) (by decide) (by decide) (by decide)
private lemma c0_011011 : ¬ (altBBGraph hollomE hollomT ![0,1,1,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_011100 : (altBBGraph hollomE hollomT ![0,1,1,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((1 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((1 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((4 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((6 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((6 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((7 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_011101 : ¬ (altBBGraph hollomE hollomT ![0,1,1,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_011110 : (altBBGraph hollomE hollomT ![0,1,1,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  hop (b := ((1 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((1 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((4 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((5 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (0 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c0_011111 : ¬ (altBBGraph hollomE hollomT ![0,1,1,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_100000 : ¬ (altBBGraph hollomE hollomT ![1,0,0,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_100001 : ¬ (altBBGraph hollomE hollomT ![1,0,0,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_100010 : ¬ (altBBGraph hollomE hollomT ![1,0,0,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_100011 : ¬ (altBBGraph hollomE hollomT ![1,0,0,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_100100 : ¬ (altBBGraph hollomE hollomT ![1,0,0,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_100101 : ¬ (altBBGraph hollomE hollomT ![1,0,0,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_100110 : ¬ (altBBGraph hollomE hollomT ![1,0,0,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_100111 : ¬ (altBBGraph hollomE hollomT ![1,0,0,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_101000 : ¬ (altBBGraph hollomE hollomT ![1,0,1,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_101001 : ¬ (altBBGraph hollomE hollomT ![1,0,1,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_101010 : ¬ (altBBGraph hollomE hollomT ![1,0,1,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_101011 : ¬ (altBBGraph hollomE hollomT ![1,0,1,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_101100 : ¬ (altBBGraph hollomE hollomT ![1,0,1,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_101101 : ¬ (altBBGraph hollomE hollomT ![1,0,1,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_101110 : ¬ (altBBGraph hollomE hollomT ![1,0,1,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_101111 : ¬ (altBBGraph hollomE hollomT ![1,0,1,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_110000 : ¬ (altBBGraph hollomE hollomT ![1,1,0,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_110001 : ¬ (altBBGraph hollomE hollomT ![1,1,0,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_110010 : ¬ (altBBGraph hollomE hollomT ![1,1,0,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_110011 : ¬ (altBBGraph hollomE hollomT ![1,1,0,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_110100 : ¬ (altBBGraph hollomE hollomT ![1,1,0,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_110101 : ¬ (altBBGraph hollomE hollomT ![1,1,0,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_110110 : ¬ (altBBGraph hollomE hollomT ![1,1,0,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_110111 : ¬ (altBBGraph hollomE hollomT ![1,1,0,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_111000 : ¬ (altBBGraph hollomE hollomT ![1,1,1,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_111001 : ¬ (altBBGraph hollomE hollomT ![1,1,1,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_111010 : ¬ (altBBGraph hollomE hollomT ![1,1,1,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_111011 : ¬ (altBBGraph hollomE hollomT ![1,1,1,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_111100 : ¬ (altBBGraph hollomE hollomT ![1,1,1,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_111101 : ¬ (altBBGraph hollomE hollomT ![1,1,1,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_111110 : ¬ (altBBGraph hollomE hollomT ![1,1,1,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c0_111111 : ¬ (altBBGraph hollomE hollomT ![1,1,1,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) :=
  notreach _ _ (by decide)

-- target (u10, 1)
private lemma c1_000000 : ¬ (altBBGraph hollomE hollomT ![0,0,0,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_000001 : (altBBGraph hollomE hollomT ![0,0,0,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_000010 : ¬ (altBBGraph hollomE hollomT ![0,0,0,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_000011 : (altBBGraph hollomE hollomT ![0,0,0,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_000100 : ¬ (altBBGraph hollomE hollomT ![0,0,0,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_000101 : (altBBGraph hollomE hollomT ![0,0,0,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_000110 : ¬ (altBBGraph hollomE hollomT ![0,0,0,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_000111 : (altBBGraph hollomE hollomT ![0,0,0,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_001000 : ¬ (altBBGraph hollomE hollomT ![0,0,1,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_001001 : (altBBGraph hollomE hollomT ![0,0,1,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_001010 : ¬ (altBBGraph hollomE hollomT ![0,0,1,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_001011 : (altBBGraph hollomE hollomT ![0,0,1,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_001100 : ¬ (altBBGraph hollomE hollomT ![0,0,1,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_001101 : (altBBGraph hollomE hollomT ![0,0,1,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_001110 : ¬ (altBBGraph hollomE hollomT ![0,0,1,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_001111 : (altBBGraph hollomE hollomT ![0,0,1,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((2 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_010000 : ¬ (altBBGraph hollomE hollomT ![0,1,0,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_010001 : ¬ (altBBGraph hollomE hollomT ![0,1,0,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  not_reach _ (fun z => z ∈ [((0 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (1 : Fin 2)), ((2 : Fin 10), (0 : Fin 2)), ((3 : Fin 10), (0 : Fin 2)), ((4 : Fin 10), (0 : Fin 2)), ((5 : Fin 10), (0 : Fin 2)), ((6 : Fin 10), (0 : Fin 2)), ((6 : Fin 10), (1 : Fin 2)), ((7 : Fin 10), (0 : Fin 2))]) (by decide) (by decide) (by decide)
private lemma c1_010010 : ¬ (altBBGraph hollomE hollomT ![0,1,0,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_010011 : (altBBGraph hollomE hollomT ![0,1,0,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((1 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((4 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((6 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((6 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((7 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_010100 : ¬ (altBBGraph hollomE hollomT ![0,1,0,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_010101 : ¬ (altBBGraph hollomE hollomT ![0,1,0,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  not_reach _ (fun z => z ∈ [((0 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (1 : Fin 2)), ((2 : Fin 10), (0 : Fin 2)), ((3 : Fin 10), (1 : Fin 2)), ((4 : Fin 10), (1 : Fin 2))]) (by decide) (by decide) (by decide)
private lemma c1_010110 : ¬ (altBBGraph hollomE hollomT ![0,1,0,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_010111 : (altBBGraph hollomE hollomT ![0,1,0,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((1 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((1 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((3 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((7 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_011000 : ¬ (altBBGraph hollomE hollomT ![0,1,1,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_011001 : (altBBGraph hollomE hollomT ![0,1,1,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((1 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((3 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((6 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((6 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((5 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_011010 : ¬ (altBBGraph hollomE hollomT ![0,1,1,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_011011 : ¬ (altBBGraph hollomE hollomT ![0,1,1,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  not_reach _ (fun z => z ∈ [((0 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (0 : Fin 2)), ((1 : Fin 10), (1 : Fin 2)), ((2 : Fin 10), (0 : Fin 2)), ((3 : Fin 10), (0 : Fin 2)), ((4 : Fin 10), (0 : Fin 2))]) (by decide) (by decide) (by decide)
private lemma c1_011100 : ¬ (altBBGraph hollomE hollomT ![0,1,1,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_011101 : (altBBGraph hollomE hollomT ![0,1,1,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((1 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((1 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((4 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((5 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((8 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_011110 : ¬ (altBBGraph hollomE hollomT ![0,1,1,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_011111 : (altBBGraph hollomE hollomT ![0,1,1,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  hop (b := ((1 : Fin 10), (0 : Fin 2))) (by decide) <|
  hop (b := ((1 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((3 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((7 : Fin 10), (1 : Fin 2))) (by decide) <|
  hop (b := ((9 : Fin 10), (1 : Fin 2))) (by decide) <|
  Reachable.refl _
private lemma c1_100000 : ¬ (altBBGraph hollomE hollomT ![1,0,0,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_100001 : ¬ (altBBGraph hollomE hollomT ![1,0,0,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_100010 : ¬ (altBBGraph hollomE hollomT ![1,0,0,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_100011 : ¬ (altBBGraph hollomE hollomT ![1,0,0,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_100100 : ¬ (altBBGraph hollomE hollomT ![1,0,0,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_100101 : ¬ (altBBGraph hollomE hollomT ![1,0,0,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_100110 : ¬ (altBBGraph hollomE hollomT ![1,0,0,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_100111 : ¬ (altBBGraph hollomE hollomT ![1,0,0,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_101000 : ¬ (altBBGraph hollomE hollomT ![1,0,1,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_101001 : ¬ (altBBGraph hollomE hollomT ![1,0,1,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_101010 : ¬ (altBBGraph hollomE hollomT ![1,0,1,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_101011 : ¬ (altBBGraph hollomE hollomT ![1,0,1,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_101100 : ¬ (altBBGraph hollomE hollomT ![1,0,1,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_101101 : ¬ (altBBGraph hollomE hollomT ![1,0,1,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_101110 : ¬ (altBBGraph hollomE hollomT ![1,0,1,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_101111 : ¬ (altBBGraph hollomE hollomT ![1,0,1,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_110000 : ¬ (altBBGraph hollomE hollomT ![1,1,0,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_110001 : ¬ (altBBGraph hollomE hollomT ![1,1,0,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_110010 : ¬ (altBBGraph hollomE hollomT ![1,1,0,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_110011 : ¬ (altBBGraph hollomE hollomT ![1,1,0,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_110100 : ¬ (altBBGraph hollomE hollomT ![1,1,0,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_110101 : ¬ (altBBGraph hollomE hollomT ![1,1,0,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_110110 : ¬ (altBBGraph hollomE hollomT ![1,1,0,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_110111 : ¬ (altBBGraph hollomE hollomT ![1,1,0,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_111000 : ¬ (altBBGraph hollomE hollomT ![1,1,1,0,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_111001 : ¬ (altBBGraph hollomE hollomT ![1,1,1,0,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_111010 : ¬ (altBBGraph hollomE hollomT ![1,1,1,0,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_111011 : ¬ (altBBGraph hollomE hollomT ![1,1,1,0,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_111100 : ¬ (altBBGraph hollomE hollomT ![1,1,1,1,0,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_111101 : ¬ (altBBGraph hollomE hollomT ![1,1,1,1,0,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_111110 : ¬ (altBBGraph hollomE hollomT ![1,1,1,1,1,0]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)
private lemma c1_111111 : ¬ (altBBGraph hollomE hollomT ![1,1,1,1,1,1]).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) :=
  notreach _ _ (by decide)

/-! ## Assembling the sum -/

private def E6 : (Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2) ≃ (Fin 6 → Fin 2) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2]
  invFun σ := (σ 0, σ 1, σ 2, σ 3, σ 4, σ 5)
  left_inv p := by revert p; decide
  right_inv σ := by funext i; fin_cases i <;> rfl

lemma prob0 :
    altProb hollomE hollomT ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) = 12 / 64 := by
  simp only [altProb]
  rw [← Equiv.sum_comp E6]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, E6, Equiv.coe_fn_mk]
  norm_num [c0_000000, c0_000001, c0_000010, c0_000011, c0_000100, c0_000101, c0_000110, c0_000111,
    c0_001000, c0_001001, c0_001010, c0_001011, c0_001100, c0_001101, c0_001110, c0_001111,
    c0_010000, c0_010001, c0_010010, c0_010011, c0_010100, c0_010101, c0_010110, c0_010111,
    c0_011000, c0_011001, c0_011010, c0_011011, c0_011100, c0_011101, c0_011110, c0_011111,
    c0_100000, c0_100001, c0_100010, c0_100011, c0_100100, c0_100101, c0_100110, c0_100111,
    c0_101000, c0_101001, c0_101010, c0_101011, c0_101100, c0_101101, c0_101110, c0_101111,
    c0_110000, c0_110001, c0_110010, c0_110011, c0_110100, c0_110101, c0_110110, c0_110111,
    c0_111000, c0_111001, c0_111010, c0_111011, c0_111100, c0_111101, c0_111110, c0_111111
    ]

lemma prob1 :
    altProb hollomE hollomT ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) = 13 / 64 := by
  simp only [altProb]
  rw [← Equiv.sum_comp E6]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, E6, Equiv.coe_fn_mk]
  norm_num [c1_000000, c1_000001, c1_000010, c1_000011, c1_000100, c1_000101, c1_000110, c1_000111,
    c1_001000, c1_001001, c1_001010, c1_001011, c1_001100, c1_001101, c1_001110, c1_001111,
    c1_010000, c1_010001, c1_010010, c1_010011, c1_010100, c1_010101, c1_010110, c1_010111,
    c1_011000, c1_011001, c1_011010, c1_011011, c1_011100, c1_011101, c1_011110, c1_011111,
    c1_100000, c1_100001, c1_100010, c1_100011, c1_100100, c1_100101, c1_100110, c1_100111,
    c1_101000, c1_101001, c1_101010, c1_101011, c1_101100, c1_101101, c1_101110, c1_101111,
    c1_110000, c1_110001, c1_110010, c1_110011, c1_110100, c1_110101, c1_110110, c1_110111,
    c1_111000, c1_111001, c1_111010, c1_111011, c1_111100, c1_111101, c1_111110, c1_111111
    ]

end L31

theorem solution :
    altProb hollomE hollomT ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) = 12 / 64 ∧
    altProb hollomE hollomT ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) = 13 / 64 :=
  ⟨L31.prob0, L31.prob1⟩

#print axioms solution