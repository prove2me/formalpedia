-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.rpow_mul_rpow_le_of_convexOn_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:05:08.505992+00:00
-- url     : https://prove2.me/submissions/afafafca-40f7-4f84-872c-90e69ef793ba

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

noncomputable section
open MeasureTheory Set
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For convex `W` and `Z > 0`, the normalized weight `e^{-W} / Z` is log-concave:
`ρ(x)^t ρ(y)^{1-t} ≤ ρ(t x + (1 - t) y)` for `0 < t < 1`. -/
theorem solution {W : V → ℝ} (hconv : ConvexOn ℝ Set.univ W) {Z : ℝ}
    (hZ : 0 < Z) (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) ≤
      Real.exp (-W (t • x + (1 - t) • y)) / Z := by
  have hAx : 0 < Real.exp (-W x) / Z :=
    div_pos (Real.exp_pos _) hZ
  have hAy : 0 < Real.exp (-W y) / Z :=
    div_pos (Real.exp_pos _) hZ
  have hlogx :
      Real.log (Real.exp (-W x) / Z) = -W x - Real.log Z := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  have hlogy :
      Real.log (Real.exp (-W y) / Z) = -W y - Real.log Z := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  have hleft :
      (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) =
        Real.exp ((-W x - Real.log Z) * t +
          (-W y - Real.log Z) * (1 - t)) := by
    rw [Real.rpow_def_of_pos hAx, Real.rpow_def_of_pos hAy, hlogx, hlogy,
      ← Real.exp_add]
  have hright :
      Real.exp (-W (t • x + (1 - t) • y)) / Z =
        Real.exp (-W (t • x + (1 - t) • y) - Real.log Z) := by
    calc
      Real.exp (-W (t • x + (1 - t) • y)) / Z =
          Real.exp (-W (t • x + (1 - t) • y)) / Real.exp (Real.log Z) := by
            rw [Real.exp_log hZ]
      _ = Real.exp (-W (t • x + (1 - t) • y) - Real.log Z) := by
        rw [Real.exp_sub]
  rw [hleft, hright]
  apply Real.exp_le_exp.mpr
  have hW0 :=
    hconv.2 (Set.mem_univ x) (Set.mem_univ y) ht0.le
      (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  have hW :
      W (t • x + (1 - t) • y) ≤ t * W x + (1 - t) * W y := by
    simpa [smul_eq_mul] using hW0
  calc
    (-W x - Real.log Z) * t + (-W y - Real.log Z) * (1 - t) =
        -(t * W x + (1 - t) * W y) - Real.log Z := by ring
    _ ≤ -W (t • x + (1 - t) • y) - Real.log Z := by linarith
