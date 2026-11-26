-- Prove2me | solution 1 for Erdos287.chen_type_i_type_ii_exponent_margins
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T15:29:01.968796+00:00
-- url     : https://prove2.me/submissions/ddb0e5a4-ae5e-4225-b61d-313136af4915

import Mathlib

set_option autoImplicit false

/-- Exponent margins for the Chen distribution target, allowing the actual
modulus factors to run below their prescribed upper caps. -/
theorem solution (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 100000) :
    let θ : ℝ := 213 / 400
    (∀ m r s : ℝ, 3 / 10 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ θ - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧
      r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν r s : ℝ, 1 / 10 ≤ ν → ν ≤ 251 / 1000 → 0 ≤ r → 0 ≤ s →
      r + s ≥ 1 / 2 - ε → r ≤ θ - ν + 2 * ε → s ≤ ν - ε →
      r - s / 2 + ν ≤ 1 / 2 - ε ∧
      2 * r + ν ≤ 1 - ε ∧
      r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧
      r + 3 * ν / 2 ≤ 1 - ε) := by
  dsimp
  constructor
  · intro m r s hm hm' hr hs hs' hr'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · intro ν r s hν hν' hr hs hsum hr' hs'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

