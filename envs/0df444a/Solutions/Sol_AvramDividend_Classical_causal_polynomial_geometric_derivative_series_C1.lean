-- Prove2me | solution 1 for AvramDividend.Classical.causal_polynomial_geometric_derivative_series_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:49:16.583994+00:00
-- url     : https://prove2.me/submissions/fe022842-e7e7-49a2-a4be-3e6a2e5c059c

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Quadratic-geometric derivative majorants yield C1 of the summed series. -/
theorem solution
    (g g' : ℕ → ℝ → ℝ) (a b C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hg : ∀ n y, y ∈ Ioo a b → HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n, ContinuousOn (g' n) (Ioo a b))
    (hbound : ∀ n y, y ∈ Ioo a b →
      ‖g' n y‖ ≤ C * (((n : ℝ) ^ 2 + 1) * r ^ n))
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo a b)
    (hval : Summable fun n => g n y₀) :
    ContDiffOn ℝ 1 (fun y => ∑' n, g n y) (Ioo a b) := by
  let F : ℝ → ℝ := fun y => ∑' n, g n y
  let G : ℝ → ℝ := fun y => ∑' n, g' n y
  let s : Set ℝ := Ioo a b
  have hrabs : |r| < 1 := by
    simpa only [abs_of_nonneg hr0] using hr1
  have hrnorm : ‖r‖ < 1 := by
    simpa only [Real.norm_eq_abs] using hrabs
  have hpoly : Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hrnorm
  have hgeom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_abs_lt_one hrabs
  have hu : Summable (fun n : ℕ =>
      C * (((n : ℝ) ^ 2 + 1) * r ^ n)) := by
    have hsum : Summable (fun n : ℕ =>
        C * ((n : ℝ) ^ 2 * r ^ n + r ^ n)) :=
      (hpoly.add hgeom).mul_left C
    simpa only [add_mul, one_mul] using hsum
  have hcontG : ContinuousOn G s :=
    continuousOn_tsum hg' hu hbound
  have hderiv : ∀ y ∈ s, HasDerivAt F (G y) y := by
    intro y hy
    exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
      isPreconnected_Ioo hg hbound hy₀ hval hy
  have hdiff : DifferentiableOn ℝ F s := by
    intro y hy
    exact (hderiv y hy).differentiableAt.differentiableWithinAt
  have heq : EqOn (deriv F) G s := by
    intro y hy
    exact (hderiv y hy).deriv
  have hzero : ContDiffOn ℝ 0 (deriv F) s := by
    rw [contDiffOn_zero]
    exact hcontG.congr heq
  have hraw : ContDiffOn ℝ (0 + 1) F s :=
    (contDiffOn_succ_iff_deriv_of_isOpen (n := 0)
      (isOpen_Ioo : IsOpen s)).2 ⟨hdiff, by simp, hzero⟩
  simpa [F, s] using hraw
