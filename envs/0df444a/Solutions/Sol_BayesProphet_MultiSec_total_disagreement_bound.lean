-- Prove2me | solution 1 for BayesProphet.MultiSec.total_disagreement_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:51:28.380923+00:00
-- url     : https://prove2.me/submissions/0859dc9a-c5a3-4832-9d3a-7c72a7a7cc77

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary
import Theorems.Thm_BayesProphet_MultiSec_cond_disagreement_bound

namespace BayesProphet.MultiSec.TotalAux

lemma geom_bound (c : ℝ) (hc : 0 < c) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, Real.exp (-(c * t)) ≤ 1 / c := by
  set x := Real.exp (-c) with hx
  have hxt : ∀ t : ℕ, Real.exp (-(c * t)) = x ^ t := by
    intro t; rw [hx, ← Real.exp_nat_mul]; ring_nf
  simp_rw [hxt]
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by rw [hx]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have key : ∀ T : ℕ, (1 - x) * ∑ t ∈ Finset.Icc 1 T, x ^ t = x - x ^ (T + 1) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; ring
  have hS : ∑ t ∈ Finset.Icc 1 T, x ^ t ≤ x / (1 - x) := by
    rw [le_div_iff₀ (by linarith), mul_comm, key]
    have : 0 < x ^ (T + 1) := pow_pos hx0 _
    linarith
  refine le_trans hS ?_
  rw [div_le_div_iff₀ (by linarith) hc]
  have h1 : 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
  have h2 : x * Real.exp c = 1 := by rw [hx, ← Real.exp_add]; simp
  nlinarith

end BayesProphet.MultiSec.TotalAux

open BayesProphet.MultiSec BayesProphet.MultiSec.TotalAux in
theorem solution {n : ℕ} [NeZero n] (p r : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (hsum : ∑ j, p j = 1) (hr : Antitone r) (hr₀ : ∀ j, 0 ≤ r j)
    (T : ℕ) (bud : ℕ → ℕ) :
    ∑ t ∈ Finset.Icc 1 T, disagreeProb p r t (bud t) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin n),
          p j * ∑ t ∈ Finset.Icc 1 T, Real.exp (-(p j ^ 2 * t / 2)) ∧
    ∑ j ∈ Finset.univ.erase (0 : Fin n),
          p j * ∑ t ∈ Finset.Icc 1 T, Real.exp (-(p j ^ 2 * t / 2)) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin n), p j * (2 / p j ^ 2) := by
  constructor
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    unfold disagreeProb
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n))]
    have h0 := (cond_disagreement_bound p r hp hsum hr hr₀ 0 t (bud t) ht1).1 (by simp)
    rw [h0, mul_zero, zero_add]
    apply Finset.sum_le_sum
    intro j hj
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h; apply (Finset.mem_erase.mp hj).1; exact Fin.ext (by simpa using h)
    exact mul_le_mul_of_nonneg_left
      ((cond_disagreement_bound p r hp hsum hr hr₀ j t (bud t) ht1).2 hj0) (hp j).le
  · apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hp j).le
    have hc : 0 < p j ^ 2 / 2 := by have := hp j; positivity
    have := geom_bound (p j ^ 2 / 2) hc T
    have e : ∀ t : ℕ, -(p j ^ 2 * t / 2) = -(p j ^ 2 / 2 * t) := fun t => by ring
    simp_rw [e]
    refine le_trans this (le_of_eq ?_)
    field_simp
