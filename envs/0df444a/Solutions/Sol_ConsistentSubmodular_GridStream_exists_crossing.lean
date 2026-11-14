-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.exists_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:07.452326+00:00
-- url     : https://prove2.me/submissions/96dce0bc-64c2-453e-818b-1505a4a772f4

import Mathlib

section

open scoped BigOperators
open Finset

theorem solution (b : ℕ → ℝ) {h δ : ℝ} {s e : ℕ} (hse : s ≤ e) (hs : h ≤ b s)
    (he : b e < h) (hstep : ∀ t, s ≤ t → t < e → b t ≤ b (t + 1) + δ) :
    ∃ t, s ≤ t ∧ t < e ∧ h ≤ b t ∧ b t < h + δ := by
  obtain ⟨d, rfl⟩ : ∃ d, e = s + d := ⟨e - s, by omega⟩
  clear hse
  induction d generalizing s with
  | zero =>
    simp only [Nat.add_zero] at he
    linarith
  | succ d ih =>
    by_cases h1 : b (s + 1) < h
    · exact ⟨s, le_rfl, by omega, hs, by linarith [hstep s le_rfl (by omega)]⟩
    · obtain ⟨t, h1t, h2t, h3t, h4t⟩ := ih (s := s + 1) (le_of_not_gt h1)
        (by rwa [show s + 1 + d = s + (d + 1) by omega])
        (fun t ht1 ht2 => hstep t (by omega) (by omega))
      exact ⟨t, by omega, by omega, h3t, h4t⟩

end
