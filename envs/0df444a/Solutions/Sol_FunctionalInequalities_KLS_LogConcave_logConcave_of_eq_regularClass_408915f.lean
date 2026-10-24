-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_regularClass_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:28:03.559764+00:00
-- url     : https://prove2.me/submissions/547f6117-bd4a-4edc-b6b6-1429c14582f6

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_rpow_mul_rpow_le_of_convexOn_408915f

noncomputable section
open MeasureTheory Set
noncomputable section
open MeasureTheory Set
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 500000 in
theorem FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_eq_restricted_exp
    (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {W : E → ℝ} (hW : Continuous W) (hWc : ConvexOn ℝ univ W)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    IsBorellDensity (μ : Measure E) volume (K.indicator fun x => Real.exp (-W x)) := by
  let f : E → ℝ := fun x => Real.exp (-W x)
  have hf : Continuous f := Real.continuous_exp.comp hW.neg
  have hnonneg : ∀ x, 0 ≤ K.indicator f x := fun x =>
    Set.indicator_nonneg (fun y _ => (Real.exp_pos (-W y)).le) x
  refine
    { measurable := hf.measurable.indicator hK.measurableSet
      nonneg := hnonneg
      upperSemicontinuous := ?_
      logConcave := ?_
      withDensity_eq := ?_ }
  · intro x a hxa
    by_cases hx : x ∈ K
    · have hfa : f x < a := by simpa only [Set.indicator_of_mem hx] using hxa
      have ha : 0 < a := (Real.exp_pos (-W x)).trans hfa
      filter_upwards [hf.upperSemicontinuous x a hfa] with y hy
      by_cases hyK : y ∈ K
      · simpa only [Set.indicator_of_mem hyK] using hy
      · simpa only [Set.indicator_of_notMem hyK] using ha
    · have ha : 0 < a := by simpa only [Set.indicator_of_notMem hx] using hxa
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      simpa only [Set.indicator_of_notMem hy] using ha
  · intro x y t ht ht1
    by_cases hx : x ∈ K
    · by_cases hy : y ∈ K
      · have hz : t • x + (1-t) • y ∈ K :=
          hKc hx hy ht.le (by linarith) (by ring)
        simp only [Set.indicator_of_mem hx,Set.indicator_of_mem hy,Set.indicator_of_mem hz]
        simpa only [div_one] using rpow_mul_rpow_le_of_convexOn_408915f hWc
          (by norm_num : (0 : ℝ) < 1) x y ht ht1
      · rw [Set.indicator_of_notMem hy,Real.zero_rpow (by linarith : 1-t ≠ 0),mul_zero]
        exact hnonneg _
    · rw [Set.indicator_of_notMem hx,Real.zero_rpow ht.ne',zero_mul]
      exact hnonneg _
  · rw [hμ]
    congr 1
    funext x
    by_cases hx : x ∈ K <;> simp [hx]
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_restricted_exp
    (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {W : E → ℝ} (hW : Continuous W) (hWc : ConvexOn ℝ univ W)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    FunctionalInequalities.KLS.LogConcave μ :=
  IsBorellDensity.compactLogConcave (isBorellDensity_of_eq_restricted_exp μ hK hKc hW hWc hμ)
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
theorem solution
    (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {W : E → ℝ} (hW : Continuous W) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    FunctionalInequalities.KLS.LogConcave μ := by
  have hWc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : E => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he : (fun y => W y - κ / 2 * ‖y‖ ^ 2) +
        (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply,smul_eq_mul,sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  exact FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_restricted_exp μ hK hKc hW hWc hμ
