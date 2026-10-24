-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.cumulant_compactPosterior_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:08:58.298335+00:00
-- url     : https://prove2.me/submissions/c783df68-fe33-4dd7-b083-1ac073521591

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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_JointRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_LogPartition
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_logPartition_joint_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_logLaplace_compactPosterior_408915f

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
/-- **Posterior cumulants are `c`-derivatives of `ψ`**: `κ_m(μ_{c,Q}) = D_c^m ψ(c, Q)` for `m ≥ 1`. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) {m : ℕ} (hm : 1 ≤ m) :
    FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure E) m =
      iteratedFDeriv ℝ m (fun y => FunctionalInequalities.Probability.Posterior.logPartition μ y Q) c := by
  have hjoint := FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint_408915f μ hc
  have hψ : ContDiff ℝ ∞ (fun y : E => FunctionalInequalities.Probability.Posterior.logPartition μ y Q) := by
    have hmap : ContDiff ℝ ∞ (fun y : E => (y, Q)) :=
      contDiff_id.prodMk contDiff_const
    have h := hjoint.comp hmap
    convert h using 1
    rfl
  have htrans : ContDiff ℝ ∞
      (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q) := by
    have hmap : ContDiff ℝ ∞ (fun z : E => c + z) :=
      contDiff_const.add contDiff_id
    have h := hψ.comp hmap
    convert h using 1
    rfl
  have hsub :
      iteratedFDeriv ℝ m
          (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q) =
        iteratedFDeriv ℝ m (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q) -
          iteratedFDeriv ℝ m (fun _ : E => FunctionalInequalities.Probability.Posterior.logPartition μ c Q) := by
    have hfun :
        (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q) =
          (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q) -
            (fun _ : E => FunctionalInequalities.Probability.Posterior.logPartition μ c Q) := by
      funext z
      rfl
    rw [hfun]
    exact iteratedFDeriv_sub
      (htrans.of_le (WithTop.coe_le_coe.mpr le_top))
      ((contDiff_const : ContDiff ℝ ∞
        (fun _ : E => FunctionalInequalities.Probability.Posterior.logPartition μ c Q)).of_le
        (WithTop.coe_le_coe.mpr le_top))
  have hm0 : m ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hconst :
      iteratedFDeriv ℝ m (fun _ : E => FunctionalInequalities.Probability.Posterior.logPartition μ c Q) = 0 :=
    iteratedFDeriv_const_of_ne hm0 _
  have hLL :
      FunctionalInequalities.Analysis.BakryEmery.logLaplace
          (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure E) =
        (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q) := by
    funext z
    exact FunctionalInequalities.Probability.Posterior.logLaplace_compactPosterior_408915f μ hc c Q z
  unfold FunctionalInequalities.Analysis.BakryEmery.cumulant
  rw [hLL]
  calc
    iteratedFDeriv ℝ m
        (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q) 0 =
        (iteratedFDeriv ℝ m (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q) -
          iteratedFDeriv ℝ m (fun _ : E => FunctionalInequalities.Probability.Posterior.logPartition μ c Q)) 0 :=
      congrFun hsub 0
    _ = iteratedFDeriv ℝ m (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q) 0 := by
      rw [hconst]
      simp
    _ = iteratedFDeriv ℝ m (fun y : E => FunctionalInequalities.Probability.Posterior.logPartition μ y Q) (c + 0) := by
      simpa only using
        (iteratedFDeriv_comp_add_left (𝕜 := ℝ) m c 0
          (f := fun y : E => FunctionalInequalities.Probability.Posterior.logPartition μ y Q))
    _ = iteratedFDeriv ℝ m (fun y : E => FunctionalInequalities.Probability.Posterior.logPartition μ y Q) c := by
      simp
