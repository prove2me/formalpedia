-- Prove2me | solution 1 for CurvatureSubmod.LocalSearch.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:21:47.018826+00:00
-- url     : https://prove2.me/submissions/0af9ff7b-fc7f-4739-8f61-1c6cf892171a

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

set_option autoImplicit false

open CurvatureSubmod.LocalSearch

lemma csls_lin_modular {X : Type} [Fintype X] [DecidableEq X] (w : X → ℝ) (S T : Finset X) :
    linFun w (S ∪ T) + linFun w (S ∩ T) = linFun w S + linFun w T := by
  unfold linFun
  exact Finset.sum_union_inter

lemma csls_diminish {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (A : Finset X) (i : X) (hi : i ∉ A) :
    marg f (Finset.univ.erase i) i ≤ marg f A i := by
  have h := hsub (insert i A) (Finset.univ.erase i)
  have e1 : insert i A ∪ Finset.univ.erase i = Finset.univ := by
    ext x; by_cases hx : x = i <;> simp [hx]
  have e2 : insert i A ∩ Finset.univ.erase i = A := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase] at hx
      rcases hx.1 with h' | h'
      · exact absurd h' hx.2.1
      · exact h'
    · intro hx
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
      exact ⟨Or.inr hx, fun h' => hi (h' ▸ hx), Finset.mem_univ _⟩
  have e3 : insert i (Finset.univ.erase i) = Finset.univ := Finset.insert_erase (Finset.mem_univ i)
  rw [e1, e2] at h
  unfold marg
  rw [e3]
  linarith

theorem solution {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hmono : MonoInc f) (hsub : NonmonotoneSubmod.Shared.Submodular f) :
    NonmonotoneSubmod.Shared.Submodular (gMax f) ∧ MonoInc (gMax f) ∧
      ∀ A, 0 ≤ gMax f A := by
  have hmonoG : MonoInc (gMax f) := by
    intro A i
    unfold marg gMax
    by_cases hi : i ∈ A
    · rw [Finset.insert_eq_of_mem hi]; simp
    · have h1 : linFun (wMax f) (insert i A) = linFun (wMax f) A + wMax f i := by
        unfold linFun; rw [Finset.sum_insert hi]; ring
      have h2 := csls_diminish f hsub A i hi
      have h3 : wMax f i = marg f (Finset.univ.erase i) i := rfl
      unfold marg at h2 h3
      rw [h1]
      linarith
  refine ⟨?_, hmonoG, ?_⟩
  · intro S T
    unfold gMax
    have := hsub S T
    have := csls_lin_modular (wMax f) S T
    linarith
  · intro A
    induction A using Finset.induction_on with
    | empty => simp [gMax, linFun, hf0 ∅]
    | insert a A ha ih =>
      have := hmonoG A a
      unfold marg at this
      linarith
