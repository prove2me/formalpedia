-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integral_hessianSq_add_le_of_hasTemperateGrowth_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:33.826457+00:00
-- url     : https://prove2.me/submissions/9cdce035-59f0-4a93-bb14-774771e2ac6e

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Temperate
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_of_norm_le_pow_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth_readable

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gamma
variable [CompleteSpace E]
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_apply (f g : E → ℝ) (x : E) : gamma f g x = ⟪gradient f x, gradient g x⟫ := rfl
/-- `Γ(f, f) = ‖∇f‖²`: the normalisation of `Γ` carries no extra factor. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_self (f : E → ℝ) (x : E) : gamma f f x = ‖gradient f x‖ ^ 2 :=
  real_inner_self_eq_norm_sq _
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_self_fun (f : E → ℝ) : gamma f f = fun y => ‖gradient f y‖ ^ 2 :=
  funext (gamma_self f)
variable [FiniteDimensional ℝ E]
end Gamma
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section
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
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
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
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.bochner_le_temperate_integrable (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → ℝ} (hg : g.HasTemperateGrowth) : Integrable g μ := by
  obtain ⟨k, C, hb⟩ := hg.2 0
  exact integrable_of_norm_le_pow_readable μ hexp hg.1.continuous.aestronglyMeasurable
    (fun x => by simpa only [norm_iteratedFDeriv_zero] using hb x)
/-- The curvature form of (16) used in BKL Lemma 3.4: if `∇²V ≥ ρ`, then
`∫ (ℒu)² dμ ≥ ∫ ‖∇²u‖²_HS dμ + ρ ∫ ‖∇u‖² dμ` for `u ∈ 𝒜`. -/
theorem solution {V f : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v) :
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x ∂(m.tilted (-V)) + ρ * ∫ x, ‖gradient f x‖ ^ 2 ∂(m.tilted (-V)) ≤
      ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) := by
  have hgrad := FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_gradient hf
  have hdd := FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_fderiv (FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_fderiv hV)
  have h1 : (fun x => fderiv ℝ (fderiv ℝ V) x (gradient f x)).HasTemperateGrowth :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)).bilinear_hasTemperateGrowth hgrad hdd
  have hB : (fun x => bilinearIteratedFDerivTwo ℝ V x
      (gradient f x) (gradient f x)).HasTemperateGrowth :=
    (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth hgrad h1
  have hBi := FunctionalInequalities.Analysis.BakryEmery.bochner_le_temperate_integrable _ hexp hB
  have hGi : Integrable (fun x => ‖gradient f x‖ ^ 2) (m.tilted (-V)) := by
    rw [← FunctionalInequalities.Analysis.BakryEmery.gamma_self_fun f]
    exact FunctionalInequalities.Analysis.BakryEmery.bochner_le_temperate_integrable _ hexp (FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_gamma hf hf)
  rw [FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth_readable m hV hexp hf]
  apply add_le_add le_rfl
  rw [← integral_const_mul]
  exact integral_mono (hGi.const_mul ρ) hBi (fun x => hH x (gradient f x))
