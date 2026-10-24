-- Prove2me | solution 1 for FunctionalInequalities.Covariance.inner_operator_self_pos_of_affineSupport_eq_top_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:49:25.724114+00:00
-- url     : https://prove2.me/submissions/5a29d221-76f8-4ee6-9aa2-c6c40472fd9c

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.CovarianceBilin

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
/-- The affine support is the smallest closed affine subspace of full measure. -/
theorem FunctionalInequalities.Probability.affineSupport_le_of_ae_mem (μ : ProbabilityMeasure E) (A : AffineSubspace ℝ E)
    (hA : IsClosed (A : Set E)) (hμ : ∀ᵐ x ∂(μ : Measure E), x ∈ A) :
    affineSupport μ ≤ A := by
  apply affineSpan_le.mpr
  exact Measure.support_subset_of_isClosed hA hμ
end
end
end
end

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities.Covariance in
/-- A law with full affine support and finite second moment has strictly positive covariance. -/
theorem solution (μ : ProbabilityMeasure E)
    (h2 : MemLp id 2 (μ : Measure E)) (hfull : FunctionalInequalities.Probability.affineSupport μ = ⊤)
    {v : E} (hv : v ≠ 0) : 0 < ⟪FunctionalInequalities.Covariance.operator (μ : Measure E) v, v⟫ := by
  rw [FunctionalInequalities.Covariance.operator_inner, covarianceBilin_self h2]
  rcases (variance_nonneg (fun x => ⟪v, x⟫) (μ : Measure E)).lt_or_eq with h | h
  · exact h
  exfalso
  have hX : MemLp (fun x => ⟪v, x⟫) 2 (μ : Measure E) := by
    simpa only [Function.comp_def, id_eq, innerSL_apply_apply] using (innerSL ℝ v).comp_memLp' h2
  have hae := ae_eq_integral_of_variance_eq_zero hX h.symm
  let c : ℝ := ∫ x, ⟪v, x⟫ ∂(μ : Measure E)
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let H : AffineSubspace ℝ E := AffineSubspace.mk' ((c / ‖v‖ ^ 2) • v) (Submodule.span ℝ {v})ᗮ
  have hmem : ∀ᵐ x ∂(μ : Measure E), x ∈ H := by
    filter_upwards [hae] with x hx
    have hx' : ⟪v, x⟫ = c := hx
    rw [AffineSubspace.mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_right, vsub_eq_sub,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hx',
      div_mul_cancel₀ c (pow_ne_zero 2 hv'), sub_self]
  have hle := FunctionalInequalities.Probability.affineSupport_le_of_ae_mem μ H H.closed_of_finiteDimensional hmem
  rw [hfull] at hle
  have hH : H = ⊤ := top_le_iff.mp hle
  have hdir : (Submodule.span ℝ {v})ᗮ = ⊤ := by
    have hh := congrArg AffineSubspace.direction hH
    rwa [AffineSubspace.direction_mk', AffineSubspace.direction_top] at hh
  exact hv (Submodule.span_singleton_eq_bot.mp ((Submodule.orthogonal_eq_top_iff _).mp hdir))
