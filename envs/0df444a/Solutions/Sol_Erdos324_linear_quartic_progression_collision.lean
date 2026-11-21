-- Prove2me | solution 1 for Erdos324.linear_quartic_progression_collision
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-20T19:47:39.513311+00:00
-- url     : https://prove2.me/submissions/8712899c-f432-463e-bc21-6ec004870091

import Mathlib

/-!
SPDX-License-Identifier: Apache-2.0

Matt directed the investigation. OpenAI Codex (Astra) developed the construction
and Lean formalization. The arithmetic-progression construction starts from
John Leech's 1957 equal-fourth-powers identity, tabulated by Lander and Parkin,
Table I, row 5 (1966). The cofinal construction uses sum-and-difference
coordinates as in Browning, arXiv:1306.6767, section 3.
-/

theorem solution (n : ℕ) :
    let d : ℤ := -(2220222977058240 * (n : ℤ) + 379828253655132800)
    let f : ℕ → ℤ := fun x => (x : ℤ)^4 + d * (x : ℤ)
    ∃ a r s b : ℕ,
      0 < a ∧ a < r ∧ r < s ∧ s < b ∧
      0 < f a ∧ f a < f r ∧ f r < f s ∧ f s < f b ∧
      f a + f b = f r + f s := by
  refine ⟨1957*n+732443, 6821*n+733595, 9766*n+1414049, 10298*n+1414175,
    by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only
  all_goals push_cast
  · ring_nf
    positivity
  · rw [← sub_pos]
    ring_nf
    positivity
  · rw [← sub_pos]
    ring_nf
    positivity
  · rw [← sub_pos]
    ring_nf
    positivity
  · ring
