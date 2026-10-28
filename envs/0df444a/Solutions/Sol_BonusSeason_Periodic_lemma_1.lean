-- Prove2me | solution 1 for BonusSeason.Periodic.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:11:37.962451+00:00
-- url     : https://prove2.me/submissions/19433e55-041c-4294-9cca-320c7e58b2f4

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

open BonusSeason.Periodic in
theorem solution (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m) :
    (∀ M0 N0 : ℝ, 0 < M0 → 0 < N0 →
      m M0 N0 / M0 = m 1 (N0 / M0) ∧ m M0 N0 / N0 = m 1 (N0 / M0) / (N0 / M0)) ∧
    StrictMonoOn (fun n => m 1 n) (Set.Ioi 0) ∧
    StrictAntiOn (fun n => m 1 n / n) (Set.Ioi 0) := by
  obtain ⟨_, hom, hmonoA, hmonoB, _⟩ := hm
  refine ⟨?_, hmonoB 1 one_pos, ?_⟩
  · intro M0 N0 hM hN
    have h := hom M0 1 (N0 / M0) hM zero_le_one (div_nonneg hN.le hM.le)
    have e : M0 * (N0 / M0) = N0 := by field_simp
    rw [mul_one, e] at h
    constructor
    · rw [h, mul_div_cancel_left₀ _ hM.ne']
    · rw [h, div_div_eq_mul_div, mul_comm]
  · have key : ∀ n : ℝ, 0 < n → m 1 n / n = m (1 / n) 1 := by
      intro n hn
      have h := hom n (1 / n) 1 hn (by positivity) zero_le_one
      have e : n * (1 / n) = 1 := by field_simp
      rw [e, mul_one] at h
      rw [h, mul_div_cancel_left₀ _ hn.ne']
    intro a ha b hb hab
    have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    show m 1 b / b < m 1 a / a
    rw [key a ha', key b hb']
    have h1 : (0 : ℝ) < 1 / b := by positivity
    have h2 : (0 : ℝ) < 1 / a := by positivity
    exact hmonoA 1 one_pos h1 h2 (one_div_lt_one_div_of_lt ha' hab)
