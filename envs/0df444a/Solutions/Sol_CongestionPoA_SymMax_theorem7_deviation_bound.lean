-- Prove2me | solution 1 for CongestionPoA.SymMax.theorem7_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T16:33:38.864953+00:00
-- url     : https://prove2.me/submissions/3279f97f-2cf1-49fc-9771-c7ab5cfd4a17

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

set_option autoImplicit false

open CongestionPoA.SymMax in
theorem p2m_4a7a6876_load_update_le {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (A : ι → Finset E) (i : ι) (S : Finset E) (e : E) :
    load (Function.update A i S) e ≤ load A e + 1 := by
  unfold load
  calc (Finset.univ.filter (fun k => e ∈ Function.update A i S k)).card
      ≤ (insert i (Finset.univ.filter (fun k => e ∈ A k))).card := by
        apply Finset.card_le_card
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        by_cases hki : k = i
        · subst hki; exact Finset.mem_insert_self _ _
        · rw [Function.update_of_ne hki] at hk
          exact Finset.mem_insert_of_mem (by simpa using hk)
    _ ≤ _ := Finset.card_insert_le _ _

open CongestionPoA.SymMax in
theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hsym : IsSymmetric G) (hA : IsPureNash G A) (hP : IsProfile G P)
    (i j : ι) :
    cost G A i ≤ ∑ e ∈ P j, G.latency e (load A e + 1) := by
  have hS : P j ∈ G.strategies i := by rw [hsym i j]; exact hP j
  refine le_trans (hA.2 i (P j) hS) ?_
  unfold cost
  rw [Function.update_self]
  apply Finset.sum_le_sum
  intro e _
  obtain ⟨a, b, ha, _, hl⟩ := hlin
  rw [hl, hl]
  have h1 : ((load (Function.update A i (P j)) e : ℕ) : ℝ) ≤ ((load A e + 1 : ℕ) : ℝ) := by
    exact_mod_cast p2m_4a7a6876_load_update_le A i (P j) e
  have := mul_le_mul_of_nonneg_left h1 (ha e)
  linarith
