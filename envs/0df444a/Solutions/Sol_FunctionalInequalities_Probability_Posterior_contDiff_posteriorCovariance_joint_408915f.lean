-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_posteriorCovariance_joint_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:02:05.932894+00:00
-- url     : https://prove2.me/submissions/56c50f19-c07a-44ce-8dbf-c9f5a4d5ef56

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
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
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_covariance_pair_joint_408915f

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
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
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
/-- A measurable statistic bounded on the support is in `L²` of the tilt. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ f : Ω → ℝ} (hφ : Continuous φ) (hf : Measurable f) {C : ℝ}
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    MemLp f 2 ((μ : Measure Ω).tilted φ) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply (integrable_tilted_iff (integrable_exp_of_compact μ hc hφ) (fun x => f x ^ 2)).mpr
  have hd : Integrable (fun x => Real.exp (φ x) * f x ^ 2) (μ : Measure Ω) := by
    apply integrable_exp_mul_of_compact μ hc hφ (hf.pow_const 2) (C := C ^ 2) (sq_nonneg C)
    intro x hx
    rw [norm_pow]
    have hB : 0 ≤ C := (norm_nonneg (f x)).trans (hb x hx)
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x hx)
  simpa only [smul_eq_mul] using hd
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- Continuous statistics are in `L²` of every posterior of a compactly supported prior. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E)
    {f : E → ℝ} (hf : Continuous f) :
    MemLp f 2 ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  obtain ⟨C, _hC, hb⟩ := exists_bound_on_support_of_compact μ hc hf
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  exact memLp_two_tilted_of_compact μ hc hφ hf.measurable hb
end
end
end
end
end

section
noncomputable section
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
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The posterior has finite second moment. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_memLp_id_two (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    MemLp id 2 (compactPosterior μ hc c Q : Measure E) := by
  change MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q))
  have hn : MemLp (fun x : E => ‖x‖) 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    memLp_two_tilted_quadraticExponent_of_compact μ hc c Q continuous_norm
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact (memLp_two_iff_integrable_sq hn.aestronglyMeasurable).1 hn
end
end
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities
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
section Moments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An operator is the sum of its matrix entries times rank-one operators in a finite orthonormal
basis. -/
private theorem FunctionalInequalities.Probability.Posterior.operator_eq_sum_rankOne {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E) :
    A = ∑ j, ∑ i, ⟪b i, A (b j)⟫ • InnerProductSpace.rankOne ℝ (b i) (b j) := by
  apply ContinuousLinearMap.ext
  intro x
  conv_lhs => rw [← b.sum_repr' x]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    InnerProductSpace.rankOne_apply, smul_smul]
  apply Finset.sum_congr rfl
  intro j _hj
  conv_lhs => rw [← b.sum_repr' (A (b j)), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [smul_smul]
  congr 1
  ring
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
/-- **Joint smoothness of the posterior covariance** `A(c,Q) = Cov(μ_{c,Q})` on `E × (E →L[ℝ] E)`, in the
operator norm; no isotropy or symmetry of `Q` is needed. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure E)) := by
  let b := stdOrthonormalBasis ℝ E
  have he (p : E × (E →L[ℝ] E)) (i j : Fin (Module.finrank ℝ E)) :
      ⟪b i, FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure E) (b j)⟫ =
        covariance (fun x => ⟪b j, x⟫) (fun x => ⟪b i, x⟫)
          ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2)) := by
    rw [real_inner_comm, FunctionalInequalities.Covariance.operator_inner,
      covarianceBilin_apply_eq_cov (FunctionalInequalities.Probability.Posterior.compactPosterior_memLp_id_two μ hc p.1 p.2)]
    rfl
  have hs : ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => ∑ j, ∑ i,
      covariance (fun x => ⟪b j, x⟫) (fun x => ⟪b i, x⟫)
        ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2)) •
          InnerProductSpace.rankOne ℝ (b i) (b j)) :=
    ContDiff.sum (fun j _hj => ContDiff.sum (fun i _hi =>
      (FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint_408915f μ hc (b j) (b i)).smul contDiff_const))
  have hfun : (fun p : E × (E →L[ℝ] E) =>
      FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure E)) =
      fun p => ∑ j, ∑ i, covariance (fun x => ⟪b j, x⟫) (fun x => ⟪b i, x⟫)
        ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2)) •
          InnerProductSpace.rankOne ℝ (b i) (b j) := by
    funext p
    rw [operator_eq_sum_rankOne b (FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure E))]
    simp only [he]
  rw [hfun]
  exact hs
