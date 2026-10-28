-- Prove2me | solution 1 for CompOpacity.Disclosure.eq_50_53
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:42:32.206236+00:00
-- url     : https://prove2.me/submissions/ab232446-a8f9-4163-aadf-b05e46d73ea8

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

open CompOpacity.Disclosure in
theorem solution (a q n t : ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (ht : 0 ≤ t) : margStar a q n t - margNC a q n t = (q + t) ^ 4 / (2 * (1 - a) ^ 2 * (1 - 2 * a)) * Lpoly a (n / (q + t)) / ((q + t + (1 - a) * n) ^ 3 * (q + t + (1 - 2 * a) * n) ^ 3) := by
  unfold margStar margNC Lpoly
  obtain ⟨P, hP⟩ : ∃ P, P = q + t + (1 - a) * n := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = q + t + (1 - 2 * a) * n := ⟨_, rfl⟩
  have hP0 : P ≠ 0 := by
    have : 0 < (1 - a) * n := mul_pos (by linarith) hn
    rw [hP]; linarith
  have hQ0 : Q ≠ 0 := by
    have : 0 < (1 - 2 * a) * n := mul_pos (by linarith) hn
    rw [hQ]; linarith
  rw [← hP, ← hQ]
  obtain ⟨s, hs⟩ : ∃ s, s = q + t := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := by rw [hs]; positivity
  rw [← hs]
  obtain ⟨u, hu⟩ : ∃ u, u = 1 - a := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by rw [hu]; linarith
  obtain ⟨v, hv⟩ : ∃ v, v = 1 - 2 * a := ⟨_, rfl⟩
  have hv0 : v ≠ 0 := by rw [hv]; linarith
  rw [← hu, ← hv]
  field_simp
  subst hP hQ hs hu hv
  ring
