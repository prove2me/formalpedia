-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_L1_convolution_powers_continuous_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:26:56.071767+00:00
-- url     : https://prove2.me/submissions/5b09b255-68bf-4c43-8e14-1594a79c83f0

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_continuousOn_positive_causal_convolution_of_locally_bounded_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The continuity recursion for signed causal convolution powers:
positivity is unnecessary once integrability and positive-tail bounds
are given explicitly. -/
theorem solution
    (k : ℝ → ℝ) (P : ℕ → ℝ → ℝ)
    (hkint : Integrable k volume)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0)
    (hkbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |k x| ≤ M)
    (hP0 : P 0 = k)
    (hPsucc : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * P n (x - y) ∂volume)
    (hPint : ∀ n : ℕ, Integrable (P n) volume)
    (hPzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → P n x = 0)
    (hPbound : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |P n x| ≤ M) :
    ∀ n : ℕ, ContinuousOn (P n) (Ioi (0 : ℝ)) := by
  intro n
  induction n with
  | zero =>
    simpa only [hP0] using hkcont
  | succ n ih =>
    rw [hPsucc n]
    exact continuousOn_positive_causal_convolution_of_locally_bounded_integrable
      k (P n) hkint (hPint n) hkcont ih hkzero
      (hPzero n) hkbound (hPbound n)
