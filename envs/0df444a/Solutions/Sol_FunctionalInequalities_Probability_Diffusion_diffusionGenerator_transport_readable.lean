-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.diffusionGenerator_transport_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:48.10687+00:00
-- url     : https://prove2.me/submissions/26299509-3312-430a-8821-64d0356674fc

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator

noncomputable section
section Adapter
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
/-- The coordinate-free generator is invariant under a continuous linear change of
coordinates (no differentiability hypothesis is needed for a linear equivalence). -/
theorem solution {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    {d : ℕ} (Φ : V ≃L[ℝ] V') (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) :
    FunctionalInequalities.Probability.Diffusion.diffusionGenerator (FunctionalInequalities.Probability.Diffusion.transportDrift Φ b) (FunctionalInequalities.Probability.Diffusion.transportNoise Φ σ) (F ∘ Φ.symm) (Φ x) =
      FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ F x := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  let A := Φ.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have he : fderiv ℝ (F ∘ Φ.symm) = A ∘ ((fderiv ℝ F) ∘ Φ.symm) := by
    funext y
    rw [Φ.symm.comp_right_fderiv]
    ext z
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, A, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.refl_apply]
  have h₂ (u : V) :
      fderiv ℝ (fderiv ℝ (F ∘ Φ.symm)) (Φ x) (Φ u) (Φ u) =
        fderiv ℝ (fderiv ℝ F) x u u := by
    rw [he, A.comp_fderiv, Φ.symm.comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, A, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.refl_apply]
  have h₁ :
      fderiv ℝ (F ∘ Φ.symm) (Φ x) (Φ (b x)) = fderiv ℝ F x (b x) := by
    rw [Φ.symm.comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  simp only [FunctionalInequalities.Probability.Diffusion.diffusionGenerator, FunctionalInequalities.Probability.Diffusion.transportDrift, FunctionalInequalities.Probability.Diffusion.transportNoise,
    ContinuousLinearEquiv.symm_apply_apply, h₁, h₂]
