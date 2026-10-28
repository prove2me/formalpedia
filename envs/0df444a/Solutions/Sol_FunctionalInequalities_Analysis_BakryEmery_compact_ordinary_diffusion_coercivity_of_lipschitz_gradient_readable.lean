-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.compact_ordinary_diffusion_coercivity_of_lipschitz_gradient_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:55.99305+00:00
-- url     : https://prove2.me/submissions/d9734053-9fae-487b-a8d5-ab9080d1c9f6

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_sq_eq_of_lipschitz_gradient_readable

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
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

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace
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
  have hScont : Continuous (FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f) := FunctionalInequalities.Analysis.BakryEmery.continuous_hessian_square hf
  have hSsupp : HasCompactSupport (FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f) := FunctionalInequalities.Analysis.BakryEmery.compact_hessian_square hfc
  have hS : Integrable (FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f) mu :=
    hScont.integrable_of_hasCompactSupport hSsupp
  have hLap : Integrable (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2) mu := by
    have hc2 : HasCompactSupport (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2) :=
      (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_weightedLaplacian U hfc).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    have hcont2 : Continuous (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2) :=
      (FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian hU hf2).pow 2
    exact hcont2.integrable_of_hasCompactSupport hc2
  have hIdentity := FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_lipschitz_gradient_readable hU hG hL hexp hf hfc
  change (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂mu) =
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x +
      ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫ ∂mu at hIdentity
  rw [integral_add hS hQ] at hIdentity
  have hnonneg : 0 ≤ ∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x ∂mu :=
    integral_nonneg fun x => FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_nonneg f x
  exact ⟨hQ, hLap, by linarith⟩
