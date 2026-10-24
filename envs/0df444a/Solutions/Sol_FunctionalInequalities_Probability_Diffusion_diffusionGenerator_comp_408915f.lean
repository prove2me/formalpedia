-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:19:56.724343+00:00
-- url     : https://prove2.me/submissions/9c4c0832-74ee-40e9-9b68-1dc36c725954

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
section S3B1GeneratorChainRule
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities.Probability.Diffusion in
/-- **Chain rule for the generator** (Itô's formula for a composite, the step (82) of BKL arXiv:2610.05474v1):
`𝓛(Φ ∘ G) = DΦ[DG·b + ½ Σ_k D²G[σ_k, σ_k]] + ½ Σ_k D²Φ[DG·σ_k, DG·σ_k]`. -/
theorem solution {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {d : ℕ} (b : V → V) (σ : V → Fin d → V)
    (Φ : W → ℝ) (G : V → W) (x : V) (hΦ : ContDiff ℝ 2 Φ) (hG : ContDiff ℝ 2 G) :
    FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ (Φ ∘ G) x =
      fderiv ℝ Φ (G x) (fderiv ℝ G x (b x) +
          (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hΦ₂ : ContDiff ℝ (1 + 1) Φ := by
    convert hΦ using 1; norm_num
  have hG₂ : ContDiff ℝ (1 + 1) G := by
    convert hG using 1; norm_num
  have hΦf : ContDiff ℝ 1 (fderiv ℝ Φ) :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := Φ) (n := 1)).mp hΦ₂ |>.2.2
  have hGf : ContDiff ℝ 1 (fderiv ℝ G) :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := G) (n := 1)).mp hG₂ |>.2.2
  have hΦfd : Differentiable ℝ (fderiv ℝ Φ) := hΦf.differentiable_one
  have hGfd : Differentiable ℝ (fderiv ℝ G) := hGf.differentiable_one
  have hfirst :
      fderiv ℝ (Φ ∘ G) =
        fun y => fderiv ℝ Φ (G y) ∘SL fderiv ℝ G y := by
    funext y
    simpa only [Function.comp_apply] using
      (fderiv_comp y hΦd.differentiableAt hGd.differentiableAt)
  have hfirst_apply (u : V) :
      fderiv ℝ (Φ ∘ G) x u =
        fderiv ℝ Φ (G x) (fderiv ℝ G x u) := by
    rw [hfirst]
    simp only [ContinuousLinearMap.comp_apply]
  have hc :
      DifferentiableAt ℝ (fun y : V => fderiv ℝ Φ (G y)) x := by
    change DifferentiableAt ℝ ((fderiv ℝ Φ) ∘ G) x
    exact (hΦfd.comp hGd).differentiableAt
  have hd : DifferentiableAt ℝ (fderiv ℝ G) x :=
    hGfd.differentiableAt
  have hcderiv :
      fderiv ℝ (fun y : V => fderiv ℝ Φ (G y)) x =
        fderiv ℝ (fderiv ℝ Φ) (G x) ∘SL fderiv ℝ G x := by
    change fderiv ℝ ((fderiv ℝ Φ) ∘ G) x = _
    exact fderiv_comp x hΦfd.differentiableAt hGd.differentiableAt
  have hdiag (u : V) :
      fderiv ℝ (fderiv ℝ (Φ ∘ G)) x u u =
        fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x u u) +
          fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x u) (fderiv ℝ G x u) := by
    rw [hfirst, fderiv_clm_comp hc hd, hcderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  calc
    FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ (Φ ∘ G) x =
        fderiv ℝ (Φ ∘ G) x (b x) +
          (1 / 2 : ℝ) * ∑ k,
            fderiv ℝ (fderiv ℝ (Φ ∘ G)) x (σ x k) (σ x k) := rfl
    _ =
        fderiv ℝ Φ (G x) (fderiv ℝ G x (b x)) +
          (1 / 2 : ℝ) * ∑ k,
            (fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
              fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k))
                (fderiv ℝ G x (σ x k))) := by
      rw [hfirst_apply]
      exact congrArg
        (fun z : ℝ => fderiv ℝ Φ (G x) (fderiv ℝ G x (b x)) + z)
        (congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
          (Finset.sum_congr rfl (fun k hk => hdiag (σ x k))))
    _ =
        fderiv ℝ Φ (G x) (fderiv ℝ G x (b x) +
            (1 / 2 : ℝ) • ∑ k,
              fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
          (1 / 2 : ℝ) * ∑ k,
            fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k))
              (fderiv ℝ G x (σ x k)) := by
      rw [map_add, map_smul, map_sum, Finset.sum_add_distrib]
      simp only [smul_eq_mul]
      ring
