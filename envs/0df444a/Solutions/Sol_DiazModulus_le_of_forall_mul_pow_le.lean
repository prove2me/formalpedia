-- Prove2me | solution 1 for DiazModulus.le_of_forall_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:12:21.259016+00:00
-- url     : https://prove2.me/submissions/06a381fd-0b4c-4c84-b205-1de94409e1b3

import Mathlib

open Complex ComplexConjugate

/-! # Leading-coefficient extraction: `a · uⁿ ≤ b · (u + c)ⁿ` for all `u ≥ 1` gives `a ≤ b`

The elementary replacement for a limit of Hilbert polynomials (DALAG §8.4.1 at finite level).
Divide by `uⁿ` over `ℝ`: for every `u ≥ 1`, `a ≤ b · (1 + c/u)ⁿ`. As `u → ∞`, `c/u → 0`
(`tendsto_const_div_atTop_nhds_zero_nat`), so the right side tends to `b · 1ⁿ = b`, and a lower
bound that holds eventually passes to the limit (`ge_of_tendsto`). -/

namespace C11_A1

/-- `(1 + c/u)ⁿ = (u + c)ⁿ / uⁿ` for `u > 0`. -/
theorem one_add_div_pow (c n u : ℕ) (hu : (0 : ℝ) < u) :
    (1 + (c : ℝ) / u) ^ n = ((u : ℝ) + c) ^ n / (u : ℝ) ^ n := by
  rw [← div_pow, add_div, div_self hu.ne']

end C11_A1

open C11_A1 in
theorem solution (a b c n : ℕ) (h : ∀ u : ℕ, 1 ≤ u → a * u ^ n ≤ b * (u + c) ^ n) :
    a ≤ b := by
  have hlim : Filter.Tendsto (fun u : ℕ => (b : ℝ) * (1 + (c : ℝ) / u) ^ n) Filter.atTop
      (nhds ((b : ℝ) * (1 + 0) ^ n)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))).pow n).const_mul _
  have hev : ∀ᶠ u : ℕ in Filter.atTop, (a : ℝ) ≤ (b : ℝ) * (1 + (c : ℝ) / u) ^ n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with u hu
    have hu' : (0 : ℝ) < u := by exact_mod_cast hu
    have h1 : ((a * u ^ n : ℕ) : ℝ) ≤ ((b * (u + c) ^ n : ℕ) : ℝ) := by exact_mod_cast h u hu
    push_cast at h1
    rw [one_add_div_pow c n u hu', ← mul_div_assoc, le_div_iff₀ (pow_pos hu' n)]
    exact h1
  have := ge_of_tendsto hlim hev
  simp only [add_zero, one_pow, mul_one] at this
  exact_mod_cast this
