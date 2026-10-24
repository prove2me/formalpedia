-- Prove2me | solution 1 for FunctionalInequalities.Probability.exists_pos_ball_inner_sub_pos_of_mem_support_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:27:06.297359+00:00
-- url     : https://prove2.me/submissions/1d9f5983-71c9-4e93-8b88-834e9bb26159

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
/-- Around a support point strictly on the positive side of `u`: a ball of positive mass inside every open halfspace
`{x | 0 < ⟪v, x - x₀⟫}` with `v` near `u`. -/
theorem solution (μ : ProbabilityMeasure E) {x₀ u y : E}
    (hy : y ∈ (μ : Measure E).support) (hpos : 0 < ⟪u, y - x₀⟫) :
    ∃ δ > 0, ∃ r > 0, 0 < (μ : Measure E) (Metric.ball y r) ∧
      ∀ v : E, ‖v - u‖ < δ → ∀ x ∈ Metric.ball y r, 0 < ⟪v, x - x₀⟫ := by
    let c : ℝ := ⟪u, y - x₀⟫
    have hc : 0 < c := by
      dsimp [c]
      exact hpos
    let r : ℝ := c / (4 * (‖u‖ + 1))
    have hr : 0 < r := by
      dsimp [r]
      positivity
    let δ : ℝ := c / (4 * (‖y - x₀‖ + r + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    refine ⟨δ, hδ, r, hr, ?_⟩
    constructor
    · by_contra h
      have hz : (μ : Measure E) (Metric.ball y r) = 0 := by
        apply le_antisymm
        · exact le_of_not_gt h
        · positivity
      have hev :
          ∀ᶠ s : Set E in (nhds y).smallSets,
            ¬ 0 < (μ : Measure E) s := by
        refine (Filter.hasBasis_smallSets (nhds y)).mem_iff.2 ?_
        refine ⟨Metric.ball y r, Metric.ball_mem_nhds y hr, ?_⟩
        intro s hs hspos
        have hle :
            (μ : Measure E) s ≤ (μ : Measure E) (Metric.ball y r) :=
          MeasureTheory.measure_mono hs
        rw [hz] at hle
        exact (not_lt_of_ge hle) hspos
      exact (Measure.mem_support_iff.mp hy) hev
    · intro v hv x hx
      have hxy : ‖x - y‖ < r := by
        simpa [dist_eq_norm] using (Metric.mem_ball.mp hx)
      have hxnorm : ‖x - x₀‖ ≤ ‖y - x₀‖ + r := by
        calc
          ‖x - x₀‖ = ‖(x - y) + (y - x₀)‖ := by
            congr 1
            abel
          _ ≤ ‖x - y‖ + ‖y - x₀‖ := norm_add_le _ _
          _ ≤ r + ‖y - x₀‖ := by linarith
          _ = ‖y - x₀‖ + r := by ring
      have hK : 0 < ‖y - x₀‖ + r + 1 := by
        positivity
      have hterm₁ :
          ‖v - u‖ * ‖x - x₀‖ < c / 4 := by
        calc
          ‖v - u‖ * ‖x - x₀‖
              ≤ ‖v - u‖ * (‖y - x₀‖ + r) :=
            mul_le_mul_of_nonneg_left hxnorm (norm_nonneg _)
          _ ≤ ‖v - u‖ * (‖y - x₀‖ + r + 1) := by
            apply mul_le_mul_of_nonneg_left
            · linarith
            · exact norm_nonneg _
          _ < δ * (‖y - x₀‖ + r + 1) :=
            mul_lt_mul_of_pos_right hv hK
          _ = c / 4 := by
            dsimp [δ]
            field_simp
      have hterm₂ : ‖u‖ * ‖x - y‖ < c / 4 := by
        have hu : ‖u‖ < ‖u‖ + 1 := by linarith
        calc
          ‖u‖ * ‖x - y‖ ≤ ‖u‖ * r :=
            mul_le_mul_of_nonneg_left (le_of_lt hxy) (norm_nonneg _)
          _ < (‖u‖ + 1) * r :=
            mul_lt_mul_of_pos_right hu hr
          _ = c / 4 := by
            dsimp [r]
            field_simp
      have habs₁ :
          |⟪v - u, x - x₀⟫| ≤ ‖v - u‖ * ‖x - x₀‖ :=
        abs_real_inner_le_norm _ _
      have habs₂ :
          |⟪u, x - y⟫| ≤ ‖u‖ * ‖x - y‖ :=
        abs_real_inner_le_norm _ _
      have hlow₁ : -c / 4 < ⟪v - u, x - x₀⟫ := by
        have hle : -|⟪v - u, x - x₀⟫| ≤ ⟪v - u, x - x₀⟫ :=
          neg_abs_le _
        linarith
      have hlow₂ : -c / 4 < ⟪u, x - y⟫ := by
        have hle : -|⟪u, x - y⟫| ≤ ⟪u, x - y⟫ :=
          neg_abs_le _
        linarith
      have hid :
          ⟪v, x - x₀⟫ =
            c + ⟪v - u, x - x₀⟫ + ⟪u, x - y⟫ := by
        calc
          ⟪v, x - x₀⟫ =
              ⟪u, x - x₀⟫ + ⟪v - u, x - x₀⟫ := by
            rw [← inner_add_left]
            congr 1
            abel
          _ = ⟪u, (y - x₀) + (x - y)⟫ +
                ⟪v - u, x - x₀⟫ := by
            congr 1
            abel
          _ = ⟪u, y - x₀⟫ + ⟪u, x - y⟫ +
                ⟪v - u, x - x₀⟫ := by
            rw [inner_add_right]
          _ = c + ⟪v - u, x - x₀⟫ + ⟪u, x - y⟫ := by
            dsimp [c]
            ring
      rw [hid]
      linarith
