-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.mconvex_constant_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:22:09.385362+00:00
-- url     : https://prove2.me/submissions/54ff7abf-6e66-425f-9a37-220b79b5b7b7

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB

set_option autoImplicit false

namespace P103dfdc7
open DiscreteConvex.MConvexSetsB

lemma step {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hExc : ExchangeAxiomB B) (x : V → ℤ) (hx : x ∈ B) (y : V → ℤ) (hy : y ∈ B)
    (u : V) (hu : y u < x u) :
    ∃ x' ∈ B, ∑ v, x' v = ∑ v, x v ∧
      ∑ w, (x' w - y w).natAbs < ∑ w, (x w - y w).natAbs := by
  obtain ⟨v, hv, hx', -⟩ := hExc x hx y hy u hu
  simp only [SuppNeg, Set.mem_setOf_eq] at hv
  have huv : u ≠ v := by rintro rfl; omega
  refine ⟨_, hx', ?_, ?_⟩
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, CharVec, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  · apply Finset.sum_lt_sum
    · intro w _
      simp only [CharVec]
      by_cases h1 : w = u
      · subst h1
        simp only [if_true, if_neg huv]
        omega
      · by_cases h2 : w = v
        · subst h2
          simp only [if_true, if_neg h1]
          omega
        · simp only [if_neg h1, if_neg h2]
          omega
    · refine ⟨u, Finset.mem_univ _, ?_⟩
      simp only [CharVec, if_true, if_neg huv]
      omega

lemma main {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hExc : ExchangeAxiomB B) :
    ∀ x ∈ B, ∀ y ∈ B, ∑ v, x v = ∑ v, y v := by
  have key : ∀ n : ℕ, ∀ x ∈ B, ∀ y ∈ B,
      ∑ w, (x w - y w).natAbs = n → ∑ v, x v = ∑ v, y v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx y hy hn
      by_cases h1 : ∃ u, y u < x u
      · obtain ⟨u, hu⟩ := h1
        obtain ⟨x', hx'B, hs, hlt⟩ := step B hExc x hx y hy u hu
        rw [← hs]
        exact ih _ (hn ▸ hlt) x' hx'B y hy rfl
      · push_neg at h1
        by_cases h2 : ∃ u, x u < y u
        · obtain ⟨u, hu⟩ := h2
          obtain ⟨y', hy'B, hs, hlt⟩ := step B hExc y hy x hx u hu
          have hsym : ∑ w, (y w - x w).natAbs = n := by
            rw [← hn]
            exact Finset.sum_congr rfl fun w _ => by omega
          rw [← hs]
          exact (ih _ (hsym ▸ hlt) y' hy'B x hx rfl).symm
        · push_neg at h2
          have : x = y := funext fun w => le_antisymm (h1 w) (h2 w)
          rw [this]
  intro x hx y hy
  exact key _ x hx y hy rfl

end P103dfdc7

open DiscreteConvex.MConvexSetsB in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hExc : ExchangeAxiomB B) :
    ∀ x ∈ B, ∀ y ∈ B, ∑ v, x v = ∑ v, y v := by
  exact P103dfdc7.main B hExc
