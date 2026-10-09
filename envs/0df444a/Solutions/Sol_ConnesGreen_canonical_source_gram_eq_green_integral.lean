-- Prove2me | solution 1 for ConnesGreen.canonical_source_gram_eq_green_integral
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T21:44:45.441575+00:00
-- url     : https://prove2.me/submissions/224c8409-b1bf-4618-a89c-565338f34bd5

import Theorems.Thm_ConnesGreen_canonical_Green_realization_and_synthesis
import Definitions.Def_ConnesGreen_integral_certificate_kernel
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative MeasureTheory Matrix
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
private theorem source_lift_inner_helper (t : ℝ) (f : WindowL2 t) (h : Physical t) :
    ⟪sourceLift t f, h⟫_ℂ = (2 : ℂ) * ⟪f, (h : Ambient t) 1⟫_ℂ := by
  rw [sourceLift, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simp [sourceLoad, PiLp.inner_apply, Fin.sum_univ_two, inner_smul_left,
    map_ofNat]

private theorem window_L2_inner_helper (t : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (windowMeasure t)) (hg : MemLp g 2 (windowMeasure t)) :
    ⟪windowL2 t f, windowL2 t g⟫_ℂ =
      ∫ x, star (f x) * g x ∂windowMeasure t := by
  simp only [windowL2, dif_pos hf, dif_pos hg, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

theorem solution (t : ℝ) (ht : 0 < t)
    (ρ σ : CriticalZeros) :
    ⟪sourceEmbed t (actualGreenSource ρ), sourceEmbed t (actualGreenSource σ)⟫_ℂ =
      canonicalSourceGramKernel t ρ σ := by
  have rg := (canonical_Green_realization_and_synthesis t ht).2.1
  change ⟪sourceLift t (windowL2 t (actualGreenSource ρ)),
    sourceEmbed t (actualGreenSource σ)⟫_ℂ = _
  rw [source_lift_inner_helper, (rg σ).2.2.2.1]
  have he : energyVector t (greenColumn t σ) 1 =
      (1 / 2 : ℂ) • windowL2 t (greenColumn t σ) := by simp [energyVector]
  rw [he, inner_smul_right]
  have hm : (2 : ℂ) * ((1 / 2 : ℂ) *
      ⟪windowL2 t (actualGreenSource ρ), windowL2 t (greenColumn t σ)⟫_ℂ) =
      ⟪windowL2 t (actualGreenSource ρ), windowL2 t (greenColumn t σ)⟫_ℂ := by ring
  rw [hm, window_L2_inner_helper t _ _ (rg ρ).1 (rg σ).2.1.1]
  unfold windowMeasure canonicalSourceGramKernel
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -t ≤ t)]

