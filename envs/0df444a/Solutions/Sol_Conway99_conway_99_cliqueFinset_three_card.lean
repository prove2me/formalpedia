-- Prove2me | solution 1 for Conway99.conway_99_cliqueFinset_three_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-06T16:59:54.137711+00:00
-- url     : https://prove2.me/submissions/1036b540-8f04-4cf9-89e4-5cfd13c0fe5c

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph Finset

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {g : SimpleGraph V} [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) :
    (g.cliqueFinset 3).card = 231 := by
  classical
  set S : Finset (V × V × V) :=
    Finset.univ.filter
      (fun t => g.Adj t.1 t.2.1 ∧ g.Adj t.1 t.2.2 ∧ g.Adj t.2.1 t.2.2) with hS
  -- ### First count: ordered adjacent triples, counted vertex by vertex
  have hinner : ∀ v w : V, g.Adj v w →
      (∑ _u ∈ Finset.univ.filter (fun u => g.Adj v u ∧ g.Adj w u), (1 : ℕ)) = 1 := by
    intro v w hvw
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    have he : (Finset.univ.filter fun u => g.Adj v u ∧ g.Adj w u)
        = (g.commonNeighbors v w).toFinset := by
      ext u
      simp [SimpleGraph.mem_commonNeighbors]
    rw [he, Set.toFinset_card, h.of_adj v w hvw]
  have hSa : S.card = 1386 := by
    have h1 : S.card = ∑ v : V, ∑ w : V, ∑ u : V,
        (if g.Adj v w ∧ g.Adj v u ∧ g.Adj w u then 1 else 0) := by
      rw [hS, Finset.card_filter, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun v _ => by rw [Fintype.sum_prod_type]
    have h2 : ∀ v w : V, (∑ u : V, if g.Adj v w ∧ g.Adj v u ∧ g.Adj w u then (1 : ℕ) else 0)
        = if g.Adj v w then 1 else 0 := by
      intro v w
      by_cases hvw : g.Adj v w
      · simp only [hvw, true_and, if_true]
        rw [← Finset.sum_filter]
        exact hinner v w hvw
      · simp [hvw]
    have h3 : ∀ v : V, (∑ w : V, if g.Adj v w then (1 : ℕ) else 0) = 14 := by
      intro v
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      have : (Finset.univ.filter fun w => g.Adj v w) = g.neighborFinset v := by
        ext w; simp
      rw [this]
      exact h.regular v
    rw [h1]
    rw [Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => h2 v w]
    rw [Finset.sum_congr rfl fun v _ => h3 v]
    rw [Finset.sum_const, Finset.card_univ, h.card, smul_eq_mul]
  -- ### Second count: six ordered triples per triangle
  have hmap : ∀ t ∈ S, ({t.1, t.2.1, t.2.2} : Finset V) ∈ g.cliqueFinset 3 := by
    intro t ht
    rw [hS, Finset.mem_filter] at ht
    obtain ⟨-, h1, h2, h3⟩ := ht
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
    exact ⟨h1, h2, h3⟩
  have hfiber : ∀ s ∈ g.cliqueFinset 3,
      (S.filter fun t => ({t.1, t.2.1, t.2.2} : Finset V) = s).card = 6 := by
    intro s hs
    rw [SimpleGraph.mem_cliqueFinset_iff] at hs
    have hcard3 : s.card = 3 := hs.2
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard3
    obtain ⟨hAab, hAac, hAbc⟩ := SimpleGraph.is3Clique_triple_iff.mp hs
    have hset : (S.filter fun t => ({t.1, t.2.1, t.2.2} : Finset V) = {a, b, c})
        = {(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)} := by
      ext t
      obtain ⟨x, y, z⟩ := t
      simp only [Finset.mem_filter, hS, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, hsets⟩
        have hxm : x ∈ ({a, b, c} : Finset V) := by rw [← hsets]; simp
        have hym : y ∈ ({a, b, c} : Finset V) := by rw [← hsets]; simp
        have hzm : z ∈ ({a, b, c} : Finset V) := by rw [← hsets]; simp
        have hxy : x ≠ y := g.ne_of_adj h1
        have hxz : x ≠ z := g.ne_of_adj h2
        have hyz : y ≠ z := g.ne_of_adj h3
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxm hym hzm
        rcases hxm with rfl | rfl | rfl <;> rcases hym with rfl | rfl | rfl <;>
          rcases hzm with rfl | rfl | rfl <;> simp_all
      · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
          refine ⟨⟨by first | assumption | (apply SimpleGraph.Adj.symm; assumption),
              by first | assumption | (apply SimpleGraph.Adj.symm; assumption),
              by first | assumption | (apply SimpleGraph.Adj.symm; assumption)⟩, ?_⟩ <;>
          (ext u; simp; try tauto)
    rw [hset]
    simp [Finset.card_insert_of_notMem, Prod.ext_iff, hab, hac, hbc,
      Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  have hSb : S.card = ∑ _s ∈ g.cliqueFinset 3, 6 := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    exact Finset.sum_congr rfl hfiber
  rw [Finset.sum_const, smul_eq_mul] at hSb
  omega
