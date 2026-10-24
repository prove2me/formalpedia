-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integral_gammaTwo_eq_of_hasTemperateGrowth_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:48:39.139706+00:00
-- url     : https://prove2.me/submissions/aeefc0b6-9af0-4d84-969e-c027f21255dd

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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_of_norm_le_pow_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_eq_zero_of_growth_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth_408915f

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
section Gamma
variable [CompleteSpace E]
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_apply (f g : E → ℝ) (x : E) : gamma f g x = ⟪gradient f x, gradient g x⟫ := rfl
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Analysis.BakryEmery.gammaTwo_apply (U f : E → ℝ) (x : E) :
    gammaTwo U f x =
      weightedLaplacian U (fun y => gamma f f y) x / 2 - gamma f (weightedLaplacian U f) x := rfl
end Gamma
end
end
end
end
end

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
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖∇g(x)‖ = ‖∇¹g(x)‖`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one (g : E → ℝ) (x : E) :
    ‖gradient g x‖ = ‖iteratedFDeriv ℝ 1 g x‖ := by
    rw [gradient, (InnerProductSpace.toDual ℝ E).symm.norm_map,
      norm_iteratedFDeriv_one]
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
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_laplacian {f : E → ℝ} (hf : f.HasTemperateGrowth) :
    (Laplacian.laplacian f).HasTemperateGrowth := by
  let b := stdOrthonormalBasis ℝ E
  have hdd := hasTemperateGrowth_fderiv (hasTemperateGrowth_fderiv hf)
  have ht (i : Fin (Module.finrank ℝ E)) :
      (fun x => fderiv ℝ (fderiv ℝ f) x (b i) (b i)).HasTemperateGrowth := by
    have h1 : (fun x => fderiv ℝ (fderiv ℝ f) x (b i)).HasTemperateGrowth :=
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)).bilinear_hasTemperateGrowth
        (Function.HasTemperateGrowth.const (b i)) hdd
    exact (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth
      (Function.HasTemperateGrowth.const (b i)) h1
  have hs := Function.HasTemperateGrowth.sum (s := Finset.univ) (fun i _ => ht i)
  convert hs using 1
  ext x
  exact laplacian_eq_sum_fderiv_fderiv f x
omit [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_weightedLaplacian {V f : E → ℝ} (hV : V.HasTemperateGrowth)
    (hf : f.HasTemperateGrowth) : (weightedLaplacian V f).HasTemperateGrowth := by
    have hgradV : (gradient V).HasTemperateGrowth :=
      hasTemperateGrowth_gradient hV
    have hgradf : (gradient f).HasTemperateGrowth :=
      hasTemperateGrowth_gradient hf
    have hprod :
        (fun x : E => (innerSL ℝ) (gradient V x) (gradient f x)).HasTemperateGrowth :=
      ContinuousLinearMap.bilinear_hasTemperateGrowth
        (innerSL ℝ) hgradV hgradf
    have hsub :
        (fun x : E =>
          Laplacian.laplacian f x -
            (innerSL ℝ) (gradient V x) (gradient f x)).HasTemperateGrowth :=
      (hasTemperateGrowth_laplacian hf).sub hprod
    have hEq :
        weightedLaplacian V f =
          (fun x : E =>
            Laplacian.laplacian f x -
              (innerSL ℝ) (gradient V x) (gradient f x)) := by
      funext x
      rw [weightedLaplacian_apply, innerSL_apply_apply]
    rw [hEq]
    exact hsub
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_gamma {f g : E → ℝ} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (gamma f g).HasTemperateGrowth := by
    have h :
        (fun x => innerSL ℝ (gradient f x) (gradient g x)).HasTemperateGrowth :=
      ContinuousLinearMap.bilinear_hasTemperateGrowth (innerSL ℝ)
        (hasTemperateGrowth_gradient hf) (hasTemperateGrowth_gradient hg)
    have hγ :
        gamma f g = fun x => innerSL ℝ (gradient f x) (gradient g x) := by
      funext x
      exact gamma_apply f g x
    rw [hγ]
    exact h
variable (m : Measure E) [m.IsAddHaarMeasure]
omit [CompleteSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.bochner_temperate_integrable {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → F} (hg : g.HasTemperateGrowth) : Integrable g μ := by
  obtain ⟨k, C, hb⟩ := hg.2 0
  exact integrable_of_norm_le_pow_408915f μ hexp hg.1.continuous.aestronglyMeasurable
    (fun x => by simpa only [norm_iteratedFDeriv_zero] using hb x)
private theorem FunctionalInequalities.Analysis.BakryEmery.bochner_temperate_generator_zero (m : Measure E) [m.IsAddHaarMeasure]
    {V g : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hg : g.HasTemperateGrowth) :
    ∫ x, weightedLaplacian V g x ∂(m.tilted (-V)) = 0 := by
  obtain ⟨kV, CV, hVb⟩ := hV.2 1
  obtain ⟨k, C, _, hb⟩ := hg.norm_iteratedFDeriv_le_uniform 2
  apply integral_weightedLaplacian_eq_zero_of_growth_408915f m
    (hV.1.of_le (WithTop.coe_le_coe.mpr le_top))
    (fun x => by simpa only [norm_gradient_eq_norm_iteratedFDeriv_one] using hVb x)
    hexp (hg.1.of_le (WithTop.coe_le_coe.mpr le_top))
  intro x
  exact ⟨by simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb 0 (by omega) x,
    hb 1 (by omega) x, hb 2 le_rfl x⟩
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- `∫ Γ₂(u) dμ = ∫ (ℒu)² dμ` for `u` and `V` of temperate growth. -/
theorem solution {V f : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) :
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.gammaTwo V f x ∂(m.tilted (-V)) = ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) := by
  have hLf := FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_weightedLaplacian hV hf
  have hG := FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_gamma hf hf
  have hLGi := bochner_temperate_integrable _ hexp
    (FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_weightedLaplacian hV hG)
  have hGi := bochner_temperate_integrable _ hexp (FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_gamma hf hLf)
  have hzero := bochner_temperate_generator_zero m hV hexp hG
  obtain ⟨kV, CV, hVb⟩ := hV.2 1
  have hibp := FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth_408915f m
    (hV.1.of_le (WithTop.coe_le_coe.mpr le_top))
    (fun x => by simpa only [FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one] using hVb x)
    hexp hf hLf
  have hsq :
      (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x ^ 2 ∂(m.tilted (-V))) =
        -(∫ x, FunctionalInequalities.Analysis.BakryEmery.gamma f (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f) x ∂(m.tilted (-V))) := by
    simpa only [pow_two, FunctionalInequalities.Analysis.BakryEmery.gamma_apply] using hibp
  simp only [FunctionalInequalities.Analysis.BakryEmery.gammaTwo_apply]
  rw [integral_sub (hLGi.div_const 2) hGi, integral_div, hzero]
  simpa using hsq.symm
