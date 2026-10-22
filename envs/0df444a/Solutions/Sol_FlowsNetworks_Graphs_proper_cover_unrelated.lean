-- Prove2me | solution 1 for FlowsNetworks.Graphs.proper_cover_unrelated
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:58:20.667179+00:00
-- url     : https://prove2.me/submissions/8a44557b-a49d-4486-b0ed-66fbf4d99f6e

import Mathlib
import Definitions.Def_FlowsNetworks_Graphs_PosetGraph
open FlowsNetworks.Graphs


theorem g69e_not_both {n : ℕ} (r : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) r]
    (X : Finset (Fin n ⊕ Fin n)) (hX : IsProperCover r X) (i : Fin n) :
    ¬ (Sum.inl i ∈ X ∧ Sum.inr i ∈ X) := by
  rintro ⟨h1, h2⟩
  obtain ⟨hc, hp⟩ := hX
  have e1 := hp (X.erase (Sum.inl i)) (Finset.erase_ssubset h1)
  have e2 := hp (X.erase (Sum.inr i)) (Finset.erase_ssubset h2)
  simp only [IsCover, not_forall] at e1 e2
  obtain ⟨a, b, hab, hn1⟩ := e1
  obtain ⟨a', b', hab', hn2⟩ := e2
  simp only [Finset.mem_erase, ne_eq, Sum.inl.injEq, reduceCtorEq, not_false_eq_true, true_and,
    not_or, not_and] at hn1 hn2
  have hb : Sum.inr b ∉ X := hn1.2
  have ha : a = i := by
    rcases hc a b hab with h | h
    · by_contra hne; exact hn1.1 hne h
    · exact absurd h hb
  have ha' : Sum.inl a' ∉ X := hn2.1
  have hb' : b' = i := by
    rcases hc a' b' hab' with h | h
    · exact absurd h ha'
    · by_contra hne; exact hn2.2 (fun e => hne (Sum.inr_injective e)) h
  subst ha hb'
  have := _root_.trans hab' hab
  rcases hc a' b this with h | h
  · exact ha' h
  · exact hb h


/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Lemma 8.2 (p. 47). Let `P = {1, …, n}` be
partially ordered by `≻` (`r`, a strict partial order) and let `G = [S, T; 𝒜]` be the bipartite
graph with `(x_i, y_j) ∈ 𝒜` iff `i ≻ j`. Corresponding to any proper cover `X ⊆ S ∪ T`, there is a
set `U ⊆ P` of mutually unrelated elements with `|X| + |U| = n`. -/
theorem solution {n : ℕ} (r : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) r]
    (X : Finset (Fin n ⊕ Fin n)) (hX : IsProperCover r X) :
    ∃ U : Finset (Fin n), MutuallyUnrelated r U ∧ X.card + U.card = n := by
  classical
  refine ⟨Finset.univ.filter (fun i => Sum.inl i ∉ X ∧ Sum.inr i ∉ X), ?_, ?_⟩
  · intro i hi j hj _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    constructor
    · intro h; rcases hX.1 i j h with h' | h'
      · exact hi.1 h'
      · exact hj.2 h'
    · intro h; rcases hX.1 j i h with h' | h'
      · exact hj.1 h'
      · exact hi.2 h'
  · have hXc : X.card = ∑ z : Fin n ⊕ Fin n, if z ∈ X then 1 else 0 := by
      rw [Finset.sum_boole]; simp
    rw [hXc, Fintype.sum_sum_type, Finset.card_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    have : ∀ i : Fin n, ((if Sum.inl i ∈ X then 1 else 0) + (if Sum.inr i ∈ X then 1 else 0) +
        (if Sum.inl i ∉ X ∧ Sum.inr i ∉ X then 1 else 0) : ℕ) = 1 := by
      intro i
      have := g69e_not_both r X hX i
      by_cases h1 : Sum.inl i ∈ X <;> by_cases h2 : Sum.inr i ∈ X <;> simp_all
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

