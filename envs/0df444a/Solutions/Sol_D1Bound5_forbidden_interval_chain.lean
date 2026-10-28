-- Prove2me | solution 1 for D1Bound5.forbidden_interval_chain
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:31:38.308238+00:00
-- url     : https://prove2.me/submissions/0ec69fc1-0f19-4644-b54b-df2d1a3086f7

import Mathlib.Algebra.Order.Archimedean.Real.Basic

section
namespace D1Bound5

/-- The logical interval-chain step used in Section common-intervals.
All endpoints are closed. The input intervals need not have distinct ends. -/
theorem _root_.solution {R : Type*} [LinearOrder R]
    (lower upper : ℕ → R) (x : R)
    (hstart : lower 0 ≤ x)
    (hoverlap : ∀ n, lower (n+1) ≤ upper n)
    (hexcluded : ∀ n, ¬ (lower n ≤ x ∧ x ≤ upper n))
    (hunbounded : ∃ n, x < lower n) : False := by
  have hle : ∀ n, lower n ≤ x := by
    intro n
    induction n with
    | zero => exact hstart
    | succ n ih =>
      have hupper : upper n < x := lt_of_not_ge fun h => hexcluded n ⟨ih, h⟩
      exact (hoverlap n).trans hupper.le
  obtain ⟨n, hn⟩ := hunbounded
  exact (not_lt_of_ge (hle n)) hn







end D1Bound5
end
