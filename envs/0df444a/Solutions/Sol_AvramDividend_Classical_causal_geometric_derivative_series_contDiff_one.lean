-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_derivative_series_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:06:50.645989+00:00
-- url     : https://prove2.me/submissions/0e09faaa-765b-4dc6-b062-35afffeb0b48

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Theorems.Thm_AvramDividend_Classical_causal_geometric_derivative_series_hasDerivAt_on_Ioo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Locally geometric derivative bounds give C1 regularity of a Neumann series. -/
theorem solution
    (g g' : ℕ → ℝ → ℝ) (a b C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hg : ∀ n y, y ∈ Ioo a b → HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n, ContinuousOn (g' n) (Ioo a b))
    (hbound : ∀ n y, y ∈ Ioo a b → ‖g' n y‖ ≤ C * r ^ n)
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo a b)
    (hval : Summable fun n => g n y₀) :
    ContDiffOn ℝ 1 (fun y => ∑' n, g n y) (Ioo a b) := by
  let F : ℝ → ℝ := fun y => ∑' n, g n y
  let G : ℝ → ℝ := fun y => ∑' n, g' n y
  let s : Set ℝ := Ioo a b
  have hrabs : |r| < 1 := by
    simpa only [abs_of_nonneg hr0] using hr1
  have hgeom : Summable (fun n : ℕ => C * r ^ n) :=
    (summable_geometric_of_abs_lt_one hrabs).mul_left C
  have hcontG : ContinuousOn G s :=
    continuousOn_tsum hg' hgeom hbound
  have hderiv : ∀ y ∈ s, HasDerivAt F (G y) y := by
    intro y hy
    exact AvramDividend.Classical.causal_geometric_derivative_series_hasDerivAt_on_Ioo
      g g' a b C r hr0 hr1 hg hbound y₀ hy₀ hval y hy
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
