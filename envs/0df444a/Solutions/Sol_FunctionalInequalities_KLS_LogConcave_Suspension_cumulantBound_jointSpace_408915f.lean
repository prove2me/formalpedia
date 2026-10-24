-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_jointSpace_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:56:49.435704+00:00
-- url     : https://prove2.me/submissions/3d55abfe-ea41-473b-9b60-d0873b5bfbf8

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_map_linearIsometryEquiv_408915f
import Theorems.Thm_FunctionalInequalities_KLS_Isotropic_map_linearIsometryEquiv_408915f

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Line
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
section
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
/-- `coordinateEquiv` sends standard basis vectors to standard basis vectors. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.coordinateEquiv_basisFun (N n : ℕ) (i : Option (Fin N × Fin n)) :
    coordinateEquiv N n (EuclideanSpace.basisFun _ ℝ i) =
      EuclideanSpace.basisFun (Fin (N * n + 1)) ℝ
        (Fintype.equivFinOfCardEq (card_option_prod N n) i) := by
  simp only [coordinateEquiv, EuclideanSpace.basisFun_apply, EuclideanSpace.piLpCongrLeft_single]
/-- Isotropy is preserved by the coordinate adapter. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.isotropic_map_coordinateEquiv {N n : ℕ} {ν : ProbabilityMeasure (JointSpace N n)}
    (hν : KLS.Isotropic ν) :
    KLS.Isotropic (ν.map (coordinateEquiv N n).continuous.measurable.aemeasurable) :=
  hν.map_linearIsometryEquiv_408915f (coordinateEquiv N n)
/-- Log-concavity is preserved by the coordinate adapter. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_map_coordinateEquiv {N n : ℕ} {ν : ProbabilityMeasure (JointSpace N n)}
    (hν : KLS.LogConcave ν) :
    KLS.LogConcave (ν.map (coordinateEquiv N n).continuous.measurable.aemeasurable) := by
  let φ := coordinateEquiv N n
  apply KLS.LogConcave.of_affineIsometry_map hν
    (ν.map φ.continuous.measurable.aemeasurable) φ.symm.toLinearIsometry.toAffineIsometry
  change Measure.map φ.symm (Measure.map φ (ν : Measure (JointSpace N n))) = _
  rw [Measure.map_map φ.symm.continuous.measurable φ.continuous.measurable]
  simp only [Function.comp_def, φ.symm_apply_apply, Measure.map_id']
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
open FunctionalInequalities.Analysis.BakryEmery in
/-- **`CumulantBound` on the joint space**, through the coordinate adapter: for an isotropic
log-concave `ν` on `JointSpace N n`, `Σ_J κ^ν_{d+1}(u, e_{J 1}, …, e_{J d})² ≤ b |u|²`, the sum
running over the joint index set (`cumulant_map_linearIsometryEquiv` pulls the cumulants back,
`Equiv.sum_comp` reindexes the sum). -/
theorem solution {N n d : ℕ} {b : ℝ} (hb : FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d b)
    {ν : ProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)} (hiso : FunctionalInequalities.KLS.Isotropic ν) (hlc : FunctionalInequalities.KLS.LogConcave ν)
    (u : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n) :
    ∑ J : Fin d → Option (Fin N × Fin n),
      FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun _ ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2 := by
  classical
  let φ := FunctionalInequalities.KLS.LogConcave.Suspension.coordinateEquiv N n
  let e := Fintype.equivFinOfCardEq (FunctionalInequalities.KLS.LogConcave.Suspension.card_option_prod N n)
  have h := hb (N * n + 1) (ν.map φ.continuous.measurable.aemeasurable)
    (FunctionalInequalities.KLS.LogConcave.Suspension.isotropic_map_coordinateEquiv hiso) (FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_map_coordinateEquiv hlc) (φ u)
  rw [LinearIsometryEquiv.norm_map] at h
  refine le_trans (le_of_eq ?_) h
  rw [← (Equiv.piCongrRight fun _ : Fin d => e).sum_comp]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hmap : ((ν.map φ.continuous.measurable.aemeasurable : ProbabilityMeasure _) :
      Measure (EuclideanSpace ℝ (Fin (N * n + 1)))) = (ν : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).map φ := by
    simp [ProbabilityMeasure.toMeasure_map]
  rw [hmap]
  have hvec : (Fin.cons (φ u) fun k => EuclideanSpace.basisFun (Fin (N * n + 1)) ℝ
      ((Equiv.piCongrRight fun _ : Fin d => e) J k)) =
      fun i => φ ((Fin.cons u fun k => EuclideanSpace.basisFun _ ℝ (J k) : Fin (d + 1) → _) i) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · simp only [Fin.cons_succ, Equiv.piCongrRight_apply]
      exact (FunctionalInequalities.KLS.LogConcave.Suspension.coordinateEquiv_basisFun N n (J k)).symm
  rw [hvec, FunctionalInequalities.Analysis.BakryEmery.cumulant_map_linearIsometryEquiv_408915f]
