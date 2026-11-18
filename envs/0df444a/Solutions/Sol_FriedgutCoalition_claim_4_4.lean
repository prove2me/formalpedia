-- Prove2me | solution 1 for FriedgutCoalition.claim_4_4
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:21:00.818669+00:00
-- url     : https://prove2.me/submissions/5fe9f241-3282-497a-9e31-6a0890ef4f73

import Mathlib
namespace FriedgutCoalition

theorem claim_4_4 (r : ℕ) (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) (i : ℕ) (hi1 : 1 ≤ i)
    (hir : i ≤ r) (k : ℕ)
    (hk : (1 - p) ^ (k + 1) < (i : ℝ) / r ∧ (i : ℝ) / r ≤ (1 - p) ^ k) :
    (i : ℝ) / r ≤ (1 - p) ^ k ∧ (1 - p) ^ k ≤ (i : ℝ) / r * (1 + 2 * p) := by
  refine ⟨hk.2, ?_⟩
  have h1 := hk.1
  rw [pow_succ] at h1
  have hq : 0 ≤ (1 - p) ^ k := pow_nonneg (by linarith) k
  have hfac : 1 ≤ (1 - p) * (1 + 2 * p) := by nlinarith
  have hir0 : 0 ≤ (i : ℝ) / r := by positivity
  calc (1 - p) ^ k ≤ (1 - p) ^ k * ((1 - p) * (1 + 2 * p)) := le_mul_of_one_le_right hq hfac
    _ = ((1 - p) ^ k * (1 - p)) * (1 + 2 * p) := by ring
    _ ≤ (i : ℝ) / r * (1 + 2 * p) := mul_le_mul_of_nonneg_right h1.le (by linarith)

end FriedgutCoalition

theorem solution (r : ℕ) (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) (i : ℕ) (hi1 : 1 ≤ i)
    (hir : i ≤ r) (k : ℕ)
    (hk : (1 - p) ^ (k + 1) < (i : ℝ) / r ∧ (i : ℝ) / r ≤ (1 - p) ^ k) :
    (i : ℝ) / r ≤ (1 - p) ^ k ∧ (1 - p) ^ k ≤ (i : ℝ) / r * (1 + 2 * p) :=
  FriedgutCoalition.claim_4_4 r p hp0 hp i hi1 hir k hk
