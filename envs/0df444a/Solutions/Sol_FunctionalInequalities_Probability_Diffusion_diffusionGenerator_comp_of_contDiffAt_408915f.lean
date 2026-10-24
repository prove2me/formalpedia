-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_of_contDiffAt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:19:58.120988+00:00
-- url     : https://prove2.me/submissions/8dbfc79d-9fbd-4ebd-a248-530c74a6d8fa

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
section S3B1LLocalChainRule
private theorem FunctionalInequalities.Probability.Diffusion.contDiffAt_fderiv_of_contDiffAt_two {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (h : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1 (fderiv ℝ f) x := by
  have h₂ : ContDiffAt ℝ ((1 : ℕ) + 1) f x := by
    convert h using 1
    norm_num
  rcases contDiffAt_succ_iff_hasFDerivAt.mp h₂ with ⟨f', hf', hf'cd⟩
  rcases hf' with ⟨u, hu, hfu⟩
  have heq : f' =ᶠ[nhds x] fderiv ℝ f := by
    filter_upwards [hu] with y hy
    exact (hfu y hy).fderiv.symm
  exact hf'cd.congr_of_eventuallyEq heq.symm
section NormedSpace
variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
private theorem FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_local_second_derivative
    (Φ : W → ℝ) (G : V → W) (x : V)
    (hΦ : ContDiffAt ℝ 2 Φ (G x)) (hG : ContDiffAt ℝ 2 G x) (u : V) :
    fderiv ℝ (fderiv ℝ (Φ ∘ G)) x u u =
      fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x u u) +
        fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x u) (fderiv ℝ G x u) := by
  have hGd : DifferentiableAt ℝ G x :=
    hG.differentiableAt (by norm_num)
  have hΦf : ContDiffAt ℝ 1 (fderiv ℝ Φ) (G x) :=
    contDiffAt_fderiv_of_contDiffAt_two hΦ
  have hGf : ContDiffAt ℝ 1 (fderiv ℝ G) x :=
    contDiffAt_fderiv_of_contDiffAt_two hG
  have hΦfd : DifferentiableAt ℝ (fderiv ℝ Φ) (G x) :=
    hΦf.differentiableAt (by norm_num)
  have hGfd : DifferentiableAt ℝ (fderiv ℝ G) x :=
    hGf.differentiableAt (by norm_num)
  have hΦev : ∀ᶠ z in nhds (G x), ContDiffAt ℝ 2 Φ z :=
    hΦ.eventually (by norm_num)
  have hΦpull : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 Φ (G y) := by
    exact hG.continuousAt.eventually hΦev
  have hfirst_event :
      fderiv ℝ (Φ ∘ G) =ᶠ[nhds x]
        (fun y => fderiv ℝ Φ (G y) ∘SL fderiv ℝ G y) := by
    filter_upwards [hG.eventually (by norm_num), hΦpull] with y hyG hyΦ
    simpa only [Function.comp_apply] using
      (fderiv_comp y
        (hyΦ.differentiableAt (by norm_num))
        (hyG.differentiableAt (by norm_num)))
  have hsecond :
      fderiv ℝ (fderiv ℝ (Φ ∘ G)) x =
        fderiv ℝ (fun y => fderiv ℝ Φ (G y) ∘SL fderiv ℝ G y) x :=
    hfirst_event.fderiv_eq
  have hc :
      DifferentiableAt ℝ (fun y : V => fderiv ℝ Φ (G y)) x := by
    change DifferentiableAt ℝ ((fderiv ℝ Φ) ∘ G) x
    exact hΦfd.comp x hGd
  have hcderiv :
      fderiv ℝ (fun y : V => fderiv ℝ Φ (G y)) x =
        fderiv ℝ (fderiv ℝ Φ) (G x) ∘SL fderiv ℝ G x := by
    change fderiv ℝ ((fderiv ℝ Φ) ∘ G) x = _
    exact fderiv_comp x hΦfd hGd
  rw [hsecond, fderiv_clm_comp hc hGfd, hcderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities.Probability.Diffusion in
/-- **Chain rule for the generator, local form** (Itô's formula for a composite, step (82) of BKL
arXiv:2610.05474v1, at one point): if `Φ` is `C²` near `G x` and `G` is `C²` near `x`, then
`𝓛(Φ ∘ G)(x) = DΦ(G x)[DG·b + ½ Σ_k D²G[σ_k, σ_k]] + ½ Σ_k D²Φ(G x)[DG·σ_k, DG·σ_k]`. -/
theorem solution {d : ℕ} (b : V → V) (σ : V → Fin d → V)
    (Φ : W → ℝ) (G : V → W) (x : V) (hΦ : ContDiffAt ℝ 2 Φ (G x)) (hG : ContDiffAt ℝ 2 G x) :
    FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ (Φ ∘ G) x =
      fderiv ℝ Φ (G x) (fderiv ℝ G x (b x) +
          (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by
  have hΦd : DifferentiableAt ℝ Φ (G x) :=
    hΦ.differentiableAt (by norm_num)
  have hGd : DifferentiableAt ℝ G x :=
    hG.differentiableAt (by norm_num)
  have hfirst :
      fderiv ℝ (Φ ∘ G) x =
        fderiv ℝ Φ (G x) ∘SL fderiv ℝ G x := by
    simpa only [Function.comp_apply] using
      (fderiv_comp x hΦd hGd)
  have hdiag (u : V) :
      fderiv ℝ (fderiv ℝ (Φ ∘ G)) x u u =
        fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x u u) +
          fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x u) (fderiv ℝ G x u) :=
    diffusionGenerator_comp_local_second_derivative Φ G x hΦ hG u
  calc
    FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ (Φ ∘ G) x =
        fderiv ℝ (Φ ∘ G) x (b x) +
          (1 / 2 : ℝ) * ∑ k,
            fderiv ℝ (fderiv ℝ (Φ ∘ G)) x (σ x k) (σ x k) := rfl
    _ =
        fderiv ℝ Φ (G x) (fderiv ℝ G x (b x)) +
          (1 / 2 : ℝ) * ∑ k,
            (fderiv ℝ Φ (G x)
                (fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
              fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k))
                (fderiv ℝ G x (σ x k))) := by
      have hsum :
          (1 / 2 : ℝ) * ∑ k,
              fderiv ℝ (fderiv ℝ (Φ ∘ G)) x (σ x k) (σ x k) =
            (1 / 2 : ℝ) * ∑ k,
              (fderiv ℝ Φ (G x)
                  (fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
                fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k))
                  (fderiv ℝ G x (σ x k))) := by
        apply congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
        exact Finset.sum_congr rfl (fun k _hk => hdiag (σ x k))
      rw [hfirst]
      simp only [ContinuousLinearMap.comp_apply]
      exact congrArg
        (fun z : ℝ => fderiv ℝ Φ (G x) (fderiv ℝ G x (b x)) + z) hsum
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
