-- Prove2me | solution 1 for EulerMascheroni.P2.foundation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:02:58.812081+00:00
-- url     : https://prove2.me/submissions/fb6345bd-a4ad-4415-8b71-16bf0e419a7d

import Definitions.Def_eulerMascheroni_p2Approximation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open EulerMascheroni.P2

private lemma coefficient_nonneg (n k : ℕ) : 0 ≤ coefficient n k := by
  unfold coefficient
  positivity

private lemma Q_pos (n : ℕ) : 0 < Q n := by
  unfold Q
  apply Finset.sum_pos'
  · intro k _
    exact coefficient_nonneg n k
  · exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), by simp [coefficient]⟩

private lemma cosine_value : Real.cos theta = (Real.sqrt 5 - 1) / 4 := by
  unfold theta
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
    Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

/-- Positivity of every explicit denominator and the exact corrected rate. -/
theorem solution :
    (∀ n : ℕ, 0 < Q n) ∧
    rate = (25 - 5 * Real.sqrt 5) / 4 ∧
    0 < rate ∧ rate < 5 := by
  refine ⟨Q_pos, ?_, ?_, ?_⟩
  · unfold rate
    rw [cosine_value]
    ring
  · unfold rate
    rw [cosine_value]
    have hs := Real.sqrt_nonneg (5 : ℝ)
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    nlinarith
  · unfold rate
    rw [cosine_value]
    have hs := Real.sqrt_nonneg (5 : ℝ)
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    nlinarith

#print axioms solution
