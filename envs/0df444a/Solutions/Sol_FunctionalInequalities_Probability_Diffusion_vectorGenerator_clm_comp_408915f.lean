-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.vectorGenerator_clm_comp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:12:13.327984+00:00
-- url     : https://prove2.me/submissions/7da56d1a-1edf-4715-9cfb-0e89ef8e33d7

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_VectorGenerator
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
open scoped Topology
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
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
section NormedSpace
variable {W W' : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']
/-- The derivative of a continuous linear map applied to a differentiable function. -/
theorem FunctionalInequalities.Probability.Diffusion.fderiv_clm_comp_apply_vec (ℓ : W →L[ℝ] W') {G : V → W} {x : V}
    (hG : DifferentiableAt ℝ G x) (v : V) :
    fderiv ℝ (fun y => ℓ (G y)) x v = ℓ (fderiv ℝ G x v) := by
  exact congrArg (fun q : V →L[ℝ] W' => q v)
    (ℓ.hasFDerivAt.comp x hG.hasFDerivAt).fderiv
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities.Probability.Diffusion in
/-- The vector generator commutes with continuous linear maps. -/
theorem solution (b : V → V) (σ : V → Fin d → V)
    (ℓ : W →L[ℝ] W') {G : V → W} {x : V} (hG : ContDiffAt ℝ 2 G x) :
    FunctionalInequalities.Probability.Diffusion.vectorGenerator b σ (fun y => ℓ (G y)) x = ℓ (FunctionalInequalities.Probability.Diffusion.vectorGenerator b σ G x) := by
  have hG' : DifferentiableAt ℝ G x := hG.differentiableAt (by norm_num)
  have htwo : ContDiffWithinAt ℝ ((1 : WithTop ℕ∞) + 1) G Set.univ x := by
    convert hG.contDiffWithinAt using 1
    norm_num
  obtain ⟨u, hu, _, _, f', huf', hf'⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt'
      (𝕜 := ℝ) (f := G) (s := Set.univ) (x := x)
      (n := (1 : WithTop ℕ∞)) (by norm_num)).mp htwo
  have hu' : u ∈ nhds x := by
    simpa using hu
  have huf_at : ∀ y ∈ u, HasFDerivAt G (f' y) y := by
    intro y hy
    exact hasFDerivWithinAt_univ.mp (huf' y hy)
  have hf'd : DifferentiableAt ℝ f' x :=
    (contDiffWithinAt_univ.mp hf').differentiableAt (by norm_num)
  have hfg : ∀ y ∈ u, fderiv ℝ G y = f' y := by
    intro y hy
    exact (huf_at y hy).fderiv
  let L : (V →L[ℝ] W) →L[ℝ] (V →L[ℝ] W') :=
    ContinuousLinearMap.compL ℝ V W W' ℓ
  have heq : Filter.EventuallyEq (nhds x) (fderiv ℝ G) f' := by
    filter_upwards [hu'] with y hy
    exact hfg y hy
  have heq₁ :
      Filter.EventuallyEq (nhds x)
        (fderiv ℝ (fun y => ℓ (G y))) (fun y => L (f' y)) := by
    filter_upwards [hu'] with y hy
    apply ContinuousLinearMap.ext
    intro z
    calc
      fderiv ℝ (fun t => ℓ (G t)) y z = ℓ (fderiv ℝ G y z) :=
        FunctionalInequalities.Probability.Diffusion.fderiv_clm_comp_apply_vec ℓ (huf_at y hy).differentiableAt z
      _ = ℓ (f' y z) := by rw [hfg y hy]
      _ = L (f' y) z := rfl
  have hsecond (v w : V) :
      fderiv ℝ (fderiv ℝ (fun y => ℓ (G y))) x v w =
        ℓ (fderiv ℝ (fderiv ℝ G) x v w) := by
    calc
      fderiv ℝ (fderiv ℝ (fun y => ℓ (G y))) x v w =
          fderiv ℝ (fun y => L (f' y)) x v w := by
            rw [heq₁.fderiv_eq]
      _ = L (fderiv ℝ f' x v) w :=
        congrArg (fun q : V →L[ℝ] W' => q w)
          (FunctionalInequalities.Probability.Diffusion.fderiv_clm_comp_apply_vec L hf'd v)
      _ = ℓ (fderiv ℝ f' x v w) := rfl
      _ = ℓ (fderiv ℝ (fderiv ℝ G) x v w) := by
        rw [heq.fderiv_eq]
  simp only [FunctionalInequalities.Probability.Diffusion.vectorGenerator]
  rw [FunctionalInequalities.Probability.Diffusion.fderiv_clm_comp_apply_vec ℓ hG' (b x)]
  simp_rw [hsecond]
  simp only [map_add, map_smul, map_sum]
