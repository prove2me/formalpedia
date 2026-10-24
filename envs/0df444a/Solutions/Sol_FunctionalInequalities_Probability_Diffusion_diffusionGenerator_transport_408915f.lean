-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.diffusionGenerator_transport_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:40:04.136443+00:00
-- url     : https://prove2.me/submissions/dc821cce-7afe-464b-9f4d-68982a7380da

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Fin

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Diffusion
section Adapter
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities.Probability.Diffusion in
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
