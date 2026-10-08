-- Prove2me | solution 1 for CongestionPoA.AsymSum.nash_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T16:33:36.73697+00:00
-- url     : https://prove2.me/submissions/fa94d888-22bb-4732-9032-e46f5aabeaa0

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

set_option autoImplicit false

open CongestionPoA.AsymSum in
theorem f7a3ca0e_load_update_le {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (A : ι → Finset E) (i : ι) (S : Finset E) (e : E) :
    load (Function.update A i S) e ≤ load A e + 1 := by
  unfold load
  calc (Finset.univ.filter (fun j => e ∈ Function.update A i S j)).card
      ≤ (insert i (Finset.univ.filter (fun j => e ∈ A j))).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [Finset.mem_insert, Finset.mem_filter]
        by_cases hji : j = i
        · exact Or.inl hji
        · right
          refine ⟨Finset.mem_univ _, ?_⟩
          rwa [Function.update_of_ne hji] at hj
    _ ≤ (Finset.univ.filter (fun j => e ∈ A j)).card + 1 := Finset.card_insert_le _ _

open CongestionPoA.AsymSum in
theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) (i : ι) :
    cost G A i ≤ cost G (Function.update A i (P i)) i ∧
      cost G (Function.update A i (P i)) i ≤ ∑ e ∈ P i, G.latency e (load A e + 1) := by
  refine ⟨hA.2 i (P i) (hP i), ?_⟩
  obtain ⟨a, b, ha, hb, hf⟩ := hlin
  unfold cost
  rw [Function.update_self]
  apply Finset.sum_le_sum
  intro e _
  rw [hf, hf]
  have h1 := f7a3ca0e_load_update_le A i (P i) e
  have h2 : ((load (Function.update A i (P i)) e : ℕ) : ℝ) ≤ ((load A e + 1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  have := mul_le_mul_of_nonneg_left h2 (ha e)
  linarith
