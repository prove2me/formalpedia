-- Prove2me | solution 1 for Erdos287.sieve_exponent_split
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T04:33:12.548153+00:00
-- url     : https://prove2.me/submissions/456a54b7-3ab7-4765-b28e-d45865db96e2

import Mathlib

set_option autoImplicit false

/-- Compatible Type II and Type III exponent ranges near level `7 / 13`.
The two ranges may use different factorizations of the same level. -/
theorem solution (ε ν : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10000)
    (hν : 1 / 13 ≤ ν) (hν' : ν ≤ 1 / 4) :
    let level := 7 / 13 - ε
    let cutoff := 3 * level - 1 - ν + ε
    let upperS := cutoff + 2 * (level - 1) / 3
    (0 < upperS ∧ upperS < level) ∧
    (∀ r s : ℝ, r ≤ level - ν + ε / 12 → cutoff ≤ r + s →
      r - s / 2 + ν ≤ 1 / 2 - ε / 4) ∧
    (∀ r s : ℝ, r ≤ level - upperS → s ≤ upperS → r + s ≤ cutoff →
      4 * r + 3 * s - 1 ≤ 1 - ν - ε ∧
      7 * r / 4 + 3 * s / 2 ≤ 1 - ν - ε ∧
      3 * r / 2 + 2 * s ≤ 1 - ν - ε) := by
  dsimp
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · intro r s hr hrs
    linarith
  · intro r s hr hs hrs
    exact ⟨by linarith, by linarith, by linarith⟩

