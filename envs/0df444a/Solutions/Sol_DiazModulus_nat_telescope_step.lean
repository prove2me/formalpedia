-- Prove2me | solution 1 for DiazModulus.nat_telescope_step
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:23:29.211991+00:00
-- url     : https://prove2.me/submissions/46b129fd-0bea-4d5d-b4b6-4de2e49ef8eb

import Mathlib

open Complex ComplexConjugate

/-! # One telescoping step: `u · g(u) ≤ f(2u)`

The step that replaces the polynomial argument of DALAG's Lemma 5.4 at finite level. If `g` is
monotone and `g(v + 1) + f(v) ≤ f(v + 1)` for every `v`, then by induction on `k`,
`f(u) + k · g(u) ≤ f(u + k)`: each step adds `g(u + k + 1) ≥ g(u)`. Taking `k = u` gives
`u · g(u) ≤ f(u) + u · g(u) ≤ f(2u)`. -/

namespace C11_telescopeStep

/-- `f(u) + k · g(u) ≤ f(u + k)`. -/
theorem add_mul_le (f g : ℕ → ℕ) (hg : Monotone g) (h : ∀ v, g (v + 1) + f v ≤ f (v + 1))
    (u k : ℕ) : f u + k * g u ≤ f (u + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := h (u + k)
    have h2 : g u ≤ g (u + k + 1) := hg (by omega)
    rw [Nat.succ_mul, ← Nat.add_assoc u k 1]
    omega

end C11_telescopeStep

open C11_telescopeStep in
theorem solution (f g : ℕ → ℕ) (hg : Monotone g) (h : ∀ v, g (v + 1) + f v ≤ f (v + 1)) (u : ℕ) :
    u * g u ≤ f (2 * u) := by
  have := add_mul_le f g hg h u u
  rw [show u + u = 2 * u by ring] at this
  omega
