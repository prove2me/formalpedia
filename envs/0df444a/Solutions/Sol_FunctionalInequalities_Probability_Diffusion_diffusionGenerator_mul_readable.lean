-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.diffusionGenerator_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:35.250977+00:00
-- url     : https://prove2.me/submissions/bddced82-4410-41b9-b8f3-53a22234a296

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator

noncomputable section
/-- **Product rule for the generator** (carré du champ): for `u, v` that are `C²` at `x`,
`𝓛(uv) = u 𝓛v + v 𝓛u + Σ_k Du[σ_k] Dv[σ_k]`. -/
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (b : V → V) (σ : V → Fin d → V) {u v : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ (fun y => u y * v y) x =
      u x * FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ v x + v x * FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ u x +
        ∑ k, fderiv ℝ u x (σ x k) * fderiv ℝ v x (σ x k) := by
  have hu' : DifferentiableAt ℝ u x := hu.differentiableAt (by norm_num)
  have hv' : DifferentiableAt ℝ v x := hv.differentiableAt (by norm_num)
  have hfu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfv : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hprod :
      (fun y => fderiv ℝ (fun z => u z * v z) y) =ᶠ[nhds x]
        (fun y => u y • fderiv ℝ v y + v y • fderiv ℝ u y) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hyu hyv
    exact fderiv_fun_mul (hyu.differentiableAt (by norm_num))
      (hyv.differentiableAt (by norm_num))
  have hD :
      HasFDerivAt
        (fun y => u y • fderiv ℝ v y + v y • fderiv ℝ u y)
        ((u x • fderiv ℝ (fderiv ℝ v) x +
            (fderiv ℝ u x).smulRight (fderiv ℝ v x)) +
          (v x • fderiv ℝ (fderiv ℝ u) x +
            (fderiv ℝ v x).smulRight (fderiv ℝ u x))) x :=
    (hu'.hasFDerivAt.smul hfv.hasFDerivAt).add
      (hv'.hasFDerivAt.smul hfu.hasFDerivAt)
  have hsecond (a : V) :
      fderiv ℝ (fderiv ℝ (fun y => u y * v y)) x a a =
        u x * fderiv ℝ (fderiv ℝ v) x a a +
          v x * fderiv ℝ (fderiv ℝ u) x a a +
            2 * (fderiv ℝ u x a * fderiv ℝ v x a) := by
    rw [hprod.fderiv_eq, hD.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  unfold FunctionalInequalities.Probability.Diffusion.diffusionGenerator
  rw [fderiv_fun_mul hu' hv']
  simp only [add_apply, smul_apply, smul_eq_mul]
  simp_rw [hsecond]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
