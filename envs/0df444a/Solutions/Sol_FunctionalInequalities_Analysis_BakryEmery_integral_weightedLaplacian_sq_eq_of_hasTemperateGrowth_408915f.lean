-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:49:47.062986+00:00
-- url     : https://prove2.me/submissions/b6c1949d-210b-4e28-889b-eee3b04f68fc

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_gammaTwo_eq_hessianSqStdBasis_add_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_of_norm_le_pow_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_gammaTwo_eq_of_hasTemperateGrowth_408915f

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Derivatives of functions of temperate growth have temperate growth. -/
theorem FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_fderiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → G} (hg : g.HasTemperateGrowth) : (fderiv ℝ g).HasTemperateGrowth := by
  refine ⟨hg.1.fderiv_right (by simp), fun n => ?_⟩
  obtain ⟨k, C, hb⟩ := hg.2 (n + 1)
  exact ⟨k, C, fun x => by simpa only [norm_iteratedFDeriv_fderiv] using hb x⟩
variable (m : Measure E) [m.IsAddHaarMeasure]
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_comp_linearIsometryEquiv
    (L : (E →L[ℝ] ℝ) ≃ₗᵢ[ℝ] E) {g : E → (E →L[ℝ] ℝ)}
    (hg : g.HasTemperateGrowth) : (L ∘ g).HasTemperateGrowth := by
  constructor
  · exact (LinearIsometryEquiv.contDiff L).comp hg.1
  · intro n
    obtain ⟨k, C, hC⟩ := hg.2 n
    refine ⟨k, C, fun x => ?_⟩
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_gradient {f : E → ℝ} (hf : f.HasTemperateGrowth) :
    (gradient f).HasTemperateGrowth := by
    change ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f).HasTemperateGrowth
    exact hasTemperateGrowth_comp_linearIsometryEquiv
      (InnerProductSpace.toDual ℝ E).symm (hasTemperateGrowth_fderiv hf)
variable (m : Measure E) [m.IsAddHaarMeasure]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.bochner_sq_temperate_hessian_eval {f : E → ℝ} (hf : f.HasTemperateGrowth)
    {g h : E → E} (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) :
    (fun x => bilinearIteratedFDerivTwo ℝ f x (g x) (h x)).HasTemperateGrowth := by
  have hdd := hasTemperateGrowth_fderiv (hasTemperateGrowth_fderiv hf)
  have h1 : (fun x => fderiv ℝ (fderiv ℝ f) x (g x)).HasTemperateGrowth :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)).bilinear_hasTemperateGrowth hg hdd
  exact (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth hh h1
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.bochner_sq_temperate_integrable (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → ℝ} (hg : g.HasTemperateGrowth) : Integrable g μ := by
  obtain ⟨k, C, hb⟩ := hg.2 0
  exact integrable_of_norm_le_pow_408915f μ hexp hg.1.continuous.aestronglyMeasurable
    (fun x => by simpa only [norm_iteratedFDeriv_zero] using hb x)
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **BKL (16)**, the integrated Bochner formula on `𝒜`:
`∫ (ℒu)² dμ = ∫ ‖∇²u‖²_HS dμ + ∫ ∇²V(∇u, ∇u) dμ`. -/
theorem solution {V f : E → ℝ}
    (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) :
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) =
      ∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x ∂(m.tilted (-V)) +
        ∫ x, bilinearIteratedFDerivTwo ℝ V x (gradient f x) (gradient f x) ∂(m.tilted (-V)) := by
  have hH : (FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f).HasTemperateGrowth := by
    unfold FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis
    apply Function.HasTemperateGrowth.sum
    intro i _
    apply Function.HasTemperateGrowth.sum
    intro j _
    exact (bochner_sq_temperate_hessian_eval hf
      (Function.HasTemperateGrowth.const (stdOrthonormalBasis ℝ E i))
      (Function.HasTemperateGrowth.const (stdOrthonormalBasis ℝ E j))).pow 2
  have hB := bochner_sq_temperate_hessian_eval hV
    (FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_gradient hf) (FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_gradient hf)
  rw [← FunctionalInequalities.Analysis.BakryEmery.integral_gammaTwo_eq_of_hasTemperateGrowth_408915f m hV hexp hf]
  have hpoint : FunctionalInequalities.Analysis.BakryEmery.gammaTwo V f = fun x => FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x +
      bilinearIteratedFDerivTwo ℝ V x (gradient f x) (gradient f x) := by
    funext x
    exact FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add_408915f
      (hV.1.of_le (WithTop.coe_le_coe.mpr le_top))
      (hf.1.of_le (WithTop.coe_le_coe.mpr le_top)) x
  rw [hpoint, integral_add (bochner_sq_temperate_integrable _ hexp hH)
    (bochner_sq_temperate_integrable _ hexp hB)]
