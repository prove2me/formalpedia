-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_gaussian_exponential_derivative_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:11:30.480744+00:00
-- url     : https://prove2.me/submissions/4d16c5bf-316d-4c33-aaef-37a2ceac972c

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Exponential conjugation cancels the damped Gaussian primitive derivative. -/
theorem solution
    (P H : ℕ → ℝ → ℝ) (a w : ℝ)
    (hSeries : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun z : ℝ => ∑' n : ℕ, H n z)
        (∑' n : ℕ, (P n x / a - w * H n x)) x)
    (hPsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ => P n x))
    (hHsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ => H n x)) :
    ∀ x : ℝ, 0 < x →
      HasDerivAt
        (fun z : ℝ => 1 / a + Real.exp (w * z) *
          (∑' n : ℕ, H n z))
        (Real.exp (w * x) * ((∑' n : ℕ, P n x) / a)) x := by
  intro x hx
  let S : ℝ → ℝ := fun z => ∑' n : ℕ, H n z
  have hs : (∑' n : ℕ, (P n x / a - w * H n x)) =
      (∑' n : ℕ, P n x) / a - w * S x := by
    rw [Summable.tsum_sub ((hPsum x hx).div_const a)
        ((hHsum x hx).mul_left w)]
    rw [tsum_div_const, tsum_mul_left]
  have he : HasDerivAt (fun z : ℝ => Real.exp (w * z))
      (w * Real.exp (w * x)) x := by
    simpa only [Function.comp_def, mul_one, one_mul, mul_comm] using
      ((Real.hasDerivAt_exp (w * x)).comp x
        ((hasDerivAt_id x).const_mul w))
  have hp : HasDerivAt (fun z => Real.exp (w * z) * S z)
      (w * Real.exp (w * x) * S x +
        Real.exp (w * x) * (∑' n : ℕ, (P n x / a - w * H n x))) x :=
    he.mul (hSeries x hx)
  have hg : HasDerivAt (fun z => 1 / a + Real.exp (w * z) * S z)
      (w * Real.exp (w * x) * S x +
        Real.exp (w * x) * (∑' n : ℕ, (P n x / a - w * H n x))) x := by
    exact hp.const_add (1 / a)
  have hcancel : w * Real.exp (w * x) * S x +
      Real.exp (w * x) * (∑' n : ℕ, (P n x / a - w * H n x)) =
      Real.exp (w * x) * ((∑' n : ℕ, P n x) / a) := by
    rw [hs]
    ring
  rw [hcancel] at hg
  exact hg
