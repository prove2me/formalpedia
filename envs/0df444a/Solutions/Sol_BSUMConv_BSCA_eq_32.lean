-- Prove2me | solution 1 for BSUMConv.BSCA.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:26:24.286997+00:00
-- url     : https://prove2.me/submissions/eba6d617-3169-44c7-b998-5cc510cca662

import Mathlib
import Definitions.Def_BSUMConv_BSCA_Setting

set_option autoImplicit false
open Filter Topology

theorem solution {N : ℕ} {n : Fin N → ℕ}
    (f : TsengBCD.Stationary.X n → ℝ) (hf : ContDiff ℝ 1 f)
    (x d : TsengBCD.Stationary.X n)
    (σ β αinit : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < αinit)
    (hdesc : fderiv ℝ f x d < 0) :
    ∃ j : ℕ,
      let α := αinit * β ^ j
      f x - f (x + α • d) ≥ -σ * α * fderiv ℝ f x d := by
  set D := fderiv ℝ f x d with hD
  have hf1 : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)) x
  have hline : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
    simpa using this
  have hg : HasDerivAt (fun t : ℝ => f (x + t • d)) D 0 := by
    have h2 := hf1.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact h2
  have hs := hg.tendsto_slope_zero_right
  have hlt : D < σ * D := by nlinarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (f (x + t • d) - f (x + (0:ℝ) • d)) < σ * D := by
    have := hs.eventually (gt_mem_nhds hlt)
    simpa using this
  have hlim : Tendsto (fun j : ℕ => αinit * β ^ j) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun j => ?_⟩
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul αinit
      simpa using this
    · exact mul_pos hα (pow_pos hβ0 j)
  obtain ⟨j, hj⟩ := (hlim.eventually hev).exists
  refine ⟨j, ?_⟩
  simp only at hj ⊢
  have hpos : 0 < αinit * β ^ j := mul_pos hα (pow_pos hβ0 j)
  simp only [zero_smul, add_zero, smul_eq_mul] at hj
  have := (inv_mul_lt_iff₀ hpos).1 hj
  nlinarith
