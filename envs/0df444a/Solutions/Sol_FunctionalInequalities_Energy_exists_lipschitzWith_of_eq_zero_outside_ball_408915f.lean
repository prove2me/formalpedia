-- Prove2me | solution 1 for FunctionalInequalities.Energy.exists_lipschitzWith_of_eq_zero_outside_ball_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:55:36.669966+00:00
-- url     : https://prove2.me/submissions/bb85039f-6def-4189-9995-c800265effe1

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section Reduction
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities.Energy in
/-- the bounded-support Lipschitz bound.  A locally Lipschitz function vanishing outside a ball is globally Lipschitz. -/
theorem solution {g : V → ℝ} {R : ℝ}
    (hg : LocallyLipschitz g) (hR : ∀ x, R ≤ ‖x‖ → g x = 0) :
    ∃ K : ℝ≥0, LipschitzWith K g := by
  rcases le_or_gt R 0 with hR0 | hR0
  · refine ⟨0, LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
    rw [hR y (hR0.trans (norm_nonneg y)), hR z (hR0.trans (norm_nonneg z))]
    simp
  set S : Set V := Metric.closedBall (0 : V) (R + 1) with hS
  have hScompact : IsCompact S := isCompact_closedBall _ _
  obtain ⟨K, hK⟩ := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.lipschitzOnWith_of_locallyLipschitz_of_isCompact hg hScompact
  obtain ⟨M₀, hM₀⟩ := hScompact.exists_bound_of_continuousOn hg.continuous.continuousOn
  set M : ℝ := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMbound : ∀ x, |g x| ≤ M := by
    intro x
    rcases le_or_gt ‖x‖ (R + 1) with hx | hx
    · exact le_trans (by simpa [Real.norm_eq_abs] using hM₀ x (by simpa [hS, Metric.mem_closedBall,
        dist_zero_right] using hx)) (le_max_left _ _)
    · rw [hR x (by linarith)]
      simpa using hM0
  refine ⟨(max (K : ℝ) (2 * M)).toNNReal, LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
  have hnn : (0 : ℝ) ≤ max (K : ℝ) (2 * M) := le_trans K.coe_nonneg (le_max_left _ _)
  rw [Real.coe_toNNReal _ hnn]
  have key : ∀ y z : V, ‖z‖ > R + 1 → dist (g y) (g z) ≤ max (K : ℝ) (2 * M) * dist y z := by
    intro y z hz
    have hgz : g z = 0 := hR z (by linarith)
    rcases le_or_gt R ‖y‖ with hy | hy
    · rw [hR y hy, hgz]
      simp
      positivity
    · have hd : 1 < dist y z := by
        have : ‖z‖ - ‖y‖ ≤ dist y z := by
          rw [dist_comm, dist_eq_norm]
          exact le_trans (by linarith [norm_sub_norm_le z y]) le_rfl
        linarith
      calc dist (g y) (g z) = |g y| := by rw [hgz]; simp
        _ ≤ M := hMbound y
        _ ≤ 2 * M * dist y z := by nlinarith
        _ ≤ max (K : ℝ) (2 * M) * dist y z := by
            apply mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
  rcases le_or_gt ‖y‖ (R + 1) with hy | hy
  · rcases le_or_gt ‖z‖ (R + 1) with hz | hz
    · calc dist (g y) (g z) ≤ K * dist y z :=
            hK.dist_le_mul y (by simpa [hS, Metric.mem_closedBall, dist_zero_right] using hy)
              z (by simpa [hS, Metric.mem_closedBall, dist_zero_right] using hz)
        _ ≤ max (K : ℝ) (2 * M) * dist y z :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
    · exact key y z hz
  · rw [dist_comm (g y) (g z), dist_comm y z]
    exact key z y hy
