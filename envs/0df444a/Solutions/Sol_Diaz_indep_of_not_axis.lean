-- Prove2me | solution 1 for Diaz.indep_of_not_axis
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:05:16.597157+00:00
-- url     : https://prove2.me/submissions/39195b0f-e04e-4fb6-bcc8-70d152dd2bc9

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {u : ℂ} (h1 : conj u ≠ u) (h2 : conj u ≠ -u)
    {a b : ℚ} (h : (a : ℂ) * u + (b : ℂ) * conj u = 0) : a = 0 ∧ b = 0 := by
  have hu : u ≠ 0 := by rintro rfl; exact h1 (map_zero _)
  have h' : (a : ℂ) * conj u + (b : ℂ) * u = 0 := by
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  have hab : ((a : ℂ) ^ 2 - (b : ℂ) ^ 2) * u = 0 := by
    linear_combination (a : ℂ) * h - (b : ℂ) * h'
  have hsq : (a : ℚ) ^ 2 = (b : ℚ) ^ 2 := by
    rcases mul_eq_zero.mp hab with h0 | h0
    · have : ((a : ℂ)) ^ 2 = ((b : ℂ)) ^ 2 := by linear_combination h0
      exact_mod_cast this
    · exact absurd h0 hu
  have hq : (a - b) * (a + b) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hq with hd | hd
  · have hab' : a = b := by linarith
    by_cases ha : a = 0
    · exact ⟨ha, by rw [← hab']; exact ha⟩
    · exfalso
      rw [← hab'] at h
      have hz : (a : ℂ) * (u + conj u) = 0 := by linear_combination h
      have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
      rcases mul_eq_zero.mp hz with h0 | h0
      · exact hac h0
      · exact h2 (by linear_combination h0)
  · have hab' : b = -a := by linarith
    by_cases ha : a = 0
    · exact ⟨ha, by rw [hab', ha]; ring⟩
    · exfalso
      rw [hab'] at h
      push_cast at h
      have hz : (a : ℂ) * (u - conj u) = 0 := by linear_combination h
      have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
      rcases mul_eq_zero.mp hz with h0 | h0
      · exact hac h0
      · exact h1 (by linear_combination -h0)
