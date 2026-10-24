-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_jointLaw_of_eq_tilted_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:01:19.717691+00:00
-- url     : https://prove2.me/submissions/091c35ca-967f-43b4-81cf-973066ccee21

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_convexOn_potential_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_408915f

section
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
/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted_408915f hνW hW hconv)
end
end
end
end
end

section
noncomputable section
open scoped ContDiff
open FunctionalInequalities.Analysis.BakryEmery
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
omit [InnerProductSpace ℝ E] in
/-- The suspension potential is continuous, including along the crease of its absolute value. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.continuous_potential {V f : E → ℝ} (hV : Continuous V) (hf : Continuous f)
    (beta sigma : ℝ) (N : ℕ) : Continuous (potential V f beta sigma N) := by
  unfold potential
  fun_prop
end
end
end
end
end
end

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
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- **Log-concavity of the joint law under (110)**, given (109). -/
theorem solution {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ)
    {a M β : ℝ} (hβ : 0 < β) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (heq : FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (volume.tilted fun x => -V x) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N =
      (volume : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).tilted fun p =>
        -FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))))
    (h : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (volume.tilted fun x => -V x) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) :
    FunctionalInequalities.KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)) := by
    let L : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n →ₗ[ℝ] ℝ × (Fin N → EuclideanSpace ℝ (Fin n)) :=
      { toFun := fun p =>
          (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))
        map_add' := by
          intro p q
          apply Prod.ext
          · simp
          · funext i
            ext j
            simp
        map_smul' := by
          intro c p
          apply Prod.ext
          · simp
          · funext i
            ext j
            simp }

    have hLcont :
        Continuous (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n =>
          (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      fun_prop

    have hconv :
        ConvexOn ℝ Set.univ
          (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n =>
            FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
              (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      simpa [L, Function.comp_def] using
        (FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_potential_408915f hV hf hβ.le hVa hfM N hN).comp_linearMap L

    have hpot :
        Continuous
          (fun q : ℝ × (Fin N → EuclideanSpace ℝ (Fin n)) =>
            FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N q) :=
      FunctionalInequalities.KLS.LogConcave.Suspension.continuous_potential hV.continuous hf.continuous β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N

    have hcont :
        Continuous
          (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n =>
            FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
              (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      change Continuous
        ((fun q : ℝ × (Fin N → EuclideanSpace ℝ (Fin n)) =>
            FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N q) ∘
          (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n =>
            (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))))
      exact hpot.comp hLcont

    let ν : ProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n) :=
      ⟨FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (volume.tilted fun x => -V x) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N, h⟩

    have hν :
        (ν : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)) =
          (volume : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).tilted
            (fun p =>
              -FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
                (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      simpa [ν] using heq

    change FunctionalInequalities.KLS.LogConcave ν
    exact
      FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted
        hν hcont hconv
