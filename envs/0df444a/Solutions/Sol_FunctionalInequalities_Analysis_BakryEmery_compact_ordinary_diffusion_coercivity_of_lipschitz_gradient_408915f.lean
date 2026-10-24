-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.compact_ordinary_diffusion_coercivity_of_lipschitz_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:46:29.714979+00:00
-- url     : https://prove2.me/submissions/1a12758c-efd8-421b-83f6-0f1a6f09a961

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_sq_eq_of_lipschitz_gradient_408915f

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section HessianSq
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_nonneg (f : E → ℝ) (x : E) : 0 ≤ hessianSqStdBasis f x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
end HessianSq
end
end
end
end
end

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
section Helpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
omit [CompleteSpace E] in
private lemma FunctionalInequalities.Analysis.BakryEmery.continuous_hessian_square {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (hessianSqStdBasis f) := by
  classical
  exact continuous_finsetSum _ fun _ _ =>
    continuous_finsetSum _ fun _ _ =>
      (((hf.fderiv_right (m := 1) (by decide)).continuous_fderiv one_ne_zero).clm_apply
        continuous_const |>.clm_apply continuous_const).pow 2
omit [CompleteSpace E] in
private lemma FunctionalInequalities.Analysis.BakryEmery.compact_hessian_square {f : E → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (hessianSqStdBasis f) := by
  classical
  refine ((hc.fderiv ℝ).fderiv ℝ).mono ?_
  intro x hx hz
  exact hx (by simp [hessianSqStdBasis, bilinearIteratedFDerivTwo, hz])
variable [MeasurableSpace E] [BorelSpace E]
end Helpers
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
set_option maxHeartbeats 2000000 in
/-- Ordinary diffusion coercivity at `C^{1,1}`: for a C1 globally Lipschitz potential `U` with Lipschitz gradient and
integrable `e^{-U}`, and `f ∈ C_c^∞`, the Hessian pairing `⟪D(∇U) ∇f, ∇f⟫` and `(ℒf)²` are integrable for the tilted
measure and `∫ ⟪D(∇U) ∇f, ∇f⟫ ≤ ∫ (ℒf)²`. Lipschitz-gradient sibling of `compact_ordinary_diffusion_coercivity`. -/
theorem solution
    {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal}
    (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
    (hexp : Integrable (fun x => Real.exp (-U x)) (volume : Measure E))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Integrable (fun x => ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫)
      ((volume : Measure E).tilted (-U)) ∧
    Integrable (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2)
      ((volume : Measure E).tilted (-U)) ∧
    (∫ x, ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫
        ∂((volume : Measure E).tilted (-U))) ≤
      ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂((volume : Measure E).tilted (-U)) := by
  classical
  let mu : Measure E := (volume : Measure E).tilted (-U)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by decide)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by decide)
  have hgf : Continuous (gradient f) := FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hf1
  obtain ⟨C, hC⟩ := ((FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hfc).isCompact_range hgf).isBounded.exists_norm_le
  have hb (x : E) : ‖gradient f x‖ ≤ C := hC _ ⟨x, rfl⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  have hmD : Measurable (fderiv ℝ (gradient U)) := measurable_fderiv ℝ (gradient U)
  have hev : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hmQ : Measurable (fun x => ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫) :=
    (hev.measurable.comp (hmD.prodMk hgf.measurable)).inner hgf.measurable
  have hQ : Integrable
      (fun x => ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫) mu := by
    refine (integrable_const ((G : ℝ) * C * C)).mono' hmQ.aestronglyMeasurable ?_
    apply Filter.Eventually.of_forall
    intro x
    have hop : ‖fderiv ℝ (gradient U) x‖ ≤ (G : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ hG
    have happ : ‖fderiv ℝ (gradient U) x (gradient f x)‖ ≤ (G : ℝ) * C :=
      ((fderiv ℝ (gradient U) x).le_opNorm _).trans
        (mul_le_mul hop (hb x) (norm_nonneg _) G.coe_nonneg)
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul happ (hb x) (norm_nonneg _) (mul_nonneg G.coe_nonneg hC0))
  have hScont : Continuous (FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f) := continuous_hessian_square hf
  have hSsupp : HasCompactSupport (FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f) := compact_hessian_square hfc
  have hS : Integrable (FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f) mu :=
    hScont.integrable_of_hasCompactSupport hSsupp
  have hLap : Integrable (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2) mu := by
    have hc2 : HasCompactSupport (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2) :=
      (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_weightedLaplacian U hfc).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    have hcont2 : Continuous (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2) :=
      (FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian hU hf2).pow 2
    exact hcont2.integrable_of_hasCompactSupport hc2
  have hIdentity := FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_lipschitz_gradient_408915f hU hG hL hexp hf hfc
  change (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂mu) =
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x +
      ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫ ∂mu at hIdentity
  rw [integral_add hS hQ] at hIdentity
  have hnonneg : 0 ≤ ∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x ∂mu :=
    integral_nonneg fun x => FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_nonneg f x
  exact ⟨hQ, hLap, by linarith⟩
