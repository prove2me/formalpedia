-- Prove2me | solution 1 for CongestionPoA.AsymSum.theorem1_sum_le_five_halves
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T17:44:49.802245+00:00
-- url     : https://prove2.me/submissions/c90b89aa-65c6-4a4a-a231-4ac65faed4c7

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Theorems.Thm_CongestionPoA_AsymSum_lemma1
import Theorems.Thm_CongestionPoA_AsymSum_sum_cost_bound

set_option autoImplicit false

open CongestionPoA.AsymSum in
theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ 5 / 2 * sumCost G P := by
  have sumCost_eq (Q : ι → Finset E) :
      sumCost G Q = ∑ e, (load Q e : ℝ) * G.latency e (load Q e) := by
    unfold sumCost cost
    calc
      _ = ∑ i, ∑ e : E, if e ∈ Q i then G.latency e (load Q e) else 0 := by
        simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      _ = ∑ e : E, ∑ i, if e ∈ Q i then G.latency e (load Q e) else 0 :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        simp [← Finset.sum_filter, load]
  obtain ⟨hNash, hgroup⟩ := sum_cost_bound G A P hlin hA hP
  have hbound : sumCost G A ≤
      (1 / 3 : ℝ) * sumCost G A + (5 / 3 : ℝ) * sumCost G P := by
    calc
      sumCost G A ≤ ∑ e, (load P e : ℝ) * G.latency e (load A e + 1) :=
        hgroup ▸ hNash
      _ ≤ ∑ e, ((1 / 3 : ℝ) * ((load A e : ℝ) * G.latency e (load A e)) +
          (5 / 3 : ℝ) * ((load P e : ℝ) * G.latency e (load P e))) := by
        obtain ⟨a, b, ha, hb, hf⟩ := hlin
        apply Finset.sum_le_sum
        intro e _
        rw [hf, hf, hf]
        simp only [Nat.cast_add, Nat.cast_one]
        have hslope := mul_le_mul_of_nonneg_left (lemma1 (load A e) (load P e)) (ha e)
        have hinterceptA := mul_nonneg (Nat.cast_nonneg (α := ℝ) (load A e)) (hb e)
        have hinterceptP := mul_nonneg (Nat.cast_nonneg (α := ℝ) (load P e)) (hb e)
        nlinarith
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← sumCost_eq A, ← sumCost_eq P]
  linarith
