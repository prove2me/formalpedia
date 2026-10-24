-- Prove2me | solution 1 for FunctionalInequalities.Probability.exists_mem_support_inner_sub_pos_of_mem_interior_convexHull_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:27:05.069232+00:00
-- url     : https://prove2.me/submissions/74b3a237-fa54-4d85-967d-2370b08582c3

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.Compact

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section MeasurableSpace
variable [MeasurableSpace E]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- A nonzero direction has a support point strictly on its positive side of an interior point of the convex hull of
the support. -/
theorem solution (μ : ProbabilityMeasure E) {x₀ : E}
    (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) {u : E} (hu : u ≠ 0) :
    ∃ y ∈ (μ : Measure E).support, 0 < ⟪u, y - x₀⟫ := by
    by_contra hneg
    push Not at hneg
    have hconv :
        Convex ℝ {y : E | ⟪u, y - x₀⟫ ≤ 0} := by
      intro a ha b hb α β hα hβ hab
      change ⟪u, a - x₀⟫ ≤ 0 at ha
      change ⟪u, b - x₀⟫ ≤ 0 at hb
      change ⟪u, (α • a + β • b) - x₀⟫ ≤ 0
      calc
        ⟪u, (α • a + β • b) - x₀⟫ =
            α * ⟪u, a - x₀⟫ + β * ⟪u, b - x₀⟫ := by
              simp only [inner_sub_right, inner_add_right, inner_smul_right]
              linear_combination ⟪u, x₀⟫ * hab
        _ ≤ 0 :=
          add_nonpos
            (mul_nonpos_of_nonneg_of_nonpos hα ha)
            (mul_nonpos_of_nonneg_of_nonpos hβ hb)
    have hsubset :
        convexHull ℝ (μ : Measure E).support ⊆
          {y : E | ⟪u, y - x₀⟫ ≤ 0} := by
      apply convexHull_min
      · intro y hy
        exact hneg y hy
      · exact hconv
    have hxnhds := mem_interior_iff_mem_nhds.mp hx₀
    rcases Metric.mem_nhds_iff.mp hxnhds with ⟨ε, hε, hball⟩
    have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let t : ℝ := ε / (2 * ‖u‖)
    have ht : 0 < t := by
      dsimp [t]
      positivity
    let z : E := x₀ + t • u
    have heq : t * ‖u‖ = ε / 2 := by
      dsimp [t]
      field_simp [ne_of_gt hnorm]
    have hdist : dist z x₀ < ε := by
      dsimp [z]
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht, heq]
      linarith
    have hzball : z ∈ Metric.ball x₀ ε :=
      Metric.mem_ball.mpr hdist
    have hzmem : z ∈ convexHull ℝ (μ : Measure E).support :=
      hball hzball
    have hzhalf := hsubset hzmem
    change ⟪u, z - x₀⟫ ≤ 0 at hzhalf
    have hzpos : 0 < ⟪u, z - x₀⟫ := by
      dsimp [z]
      rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq]
      positivity
    exact (not_lt_of_ge hzhalf) hzpos
