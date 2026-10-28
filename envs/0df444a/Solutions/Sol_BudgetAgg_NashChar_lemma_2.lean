-- Prove2me | solution 1 for BudgetAgg.NashChar.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:10:47.099982+00:00
-- url     : https://prove2.me/submissions/91abb54b-1c5d-4b92-9f64-a2aa9cf768e1

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

open BudgetAgg.NashChar in
theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (h : IsCoreFairShare P q) (i : Fin n) :
    1 / (n : ℝ) ≤ leontief (P i) q.1 := by
  by_contra hc
  push_neg at hc
  have hn : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by linarith
  have h1n : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact hn
  have h1n0 : 0 < 1 / (n : ℝ) := by positivity
  apply h {i} (Finset.singleton_nonempty i)
  refine ⟨P i, fun q'' i' hi' => ?_⟩
  rw [Finset.mem_singleton] at hi'
  subst hi'
  simp only [Finset.card_singleton, Nat.cast_one]
  refine lt_of_lt_of_le hc ?_
  unfold leontief
  apply Finset.le_inf'
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [le_div_iff₀ hj.2]
  have hq := q''.2.1 j
  have : 0 ≤ (1 - 1 / (n : ℝ)) * q''.1 j := mul_nonneg (by linarith) hq
  linarith
