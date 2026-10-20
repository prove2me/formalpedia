-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_tendsto_atTop_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:35:06.847471+00:00
-- url     : https://prove2.me/submissions/6aaf1ab9-d466-4033-85c2-77c36b4cb17b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology


theorem solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) :
    Tendsto (lowerGammaBoundaryLog ℓ R)
      (𝓝[≠] (0 : ℝ)) atTop := by
  have hz : Tendsto (fun y : ℝ => -Complex.I * (y:ℂ) / 2) (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun y : ℝ => -Complex.I * (y:ℂ) / 2) (𝓝 0)
          (𝓝 (-Complex.I * ((0:ℝ):ℂ) / 2)) :=
        ((continuous_const.mul Complex.continuous_ofReal).div_const 2).tendsto 0
      simp only [Complex.ofReal_zero, mul_zero, zero_div] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : y ≠ 0 := hy
      simp [hy', Complex.I_ne_zero]
  have hzG := Complex.tendsto_self_mul_Gamma_nhds_zero.comp hz
  have hev : ∀ᶠ y : ℝ in 𝓝[≠] (0:ℝ),
      ‖(-Complex.I * ((y:ℝ):ℂ) / 2) * Complex.Gamma (-Complex.I * ((y:ℝ):ℂ) / 2)‖ ∈ Ioi (1/2 : ℝ) := by
    have := ((continuous_norm.tendsto (1:ℂ)).comp hzG)
    exact this.eventually (Ioi_mem_nhds (show (1/2:ℝ) < ‖(1:ℂ)‖ by simp; norm_num))
  have habs : Tendsto (fun y : ℝ => |y|) (𝓝[≠] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (continuous_abs.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := {(0:ℝ)}ᶜ))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact abs_pos.2 hy
  have hA : Tendsto (fun y : ℝ => ‖Complex.Gamma (-Complex.I * (y:ℂ) / 2)‖) (𝓝[≠] 0) atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_inv_nhdsGT_zero.comp habs)
    filter_upwards [hev, self_mem_nhdsWithin] with y h1 hy
    have hy' : 0 < |y| := abs_pos.2 hy
    have h1' : 1/2 < ‖(-Complex.I * (y:ℂ) / 2)‖ * ‖Complex.Gamma (-Complex.I * (y:ℂ) / 2)‖ := by
      rw [← norm_mul]; exact h1
    have hn : ‖-Complex.I * (y:ℂ) / 2‖ = |y| / 2 := by simp [Complex.norm_real]
    rw [hn] at h1'
    simp only [Function.comp]
    rw [inv_eq_one_div, div_le_iff₀ hy']
    nlinarith
  have hB : Tendsto (fun y : ℝ => Real.log ‖Complex.Gamma ((ℓ:ℂ) + Complex.I * (y:ℂ) / 2)‖) (𝓝[≠] 0)
      (𝓝 (Real.log ‖Complex.Gamma ((ℓ:ℂ) + Complex.I * ((0:ℝ):ℂ) / 2)‖)) := by
    have hd : DifferentiableAt ℂ Complex.Gamma ((ℓ:ℂ) + Complex.I * ((0:ℝ):ℂ) / 2) := by
      refine Complex.differentiableAt_Gamma _ (fun m h => ?_)
      have := congrArg Complex.re h
      simp at this
      linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
    have hc : ContinuousAt (fun y : ℝ => ‖Complex.Gamma ((ℓ:ℂ) + Complex.I * (y:ℂ) / 2)‖) 0 :=
      ((hd.continuousAt).comp (x := (0:ℝ)) (f := fun y : ℝ => (ℓ:ℂ) + Complex.I * (y:ℂ) / 2)
        (by fun_prop)).norm
    have hne : ‖Complex.Gamma ((ℓ:ℂ) + Complex.I * ((0:ℝ):ℂ) / 2)‖ ≠ 0 :=
      norm_ne_zero_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
    exact (hc.log hne).tendsto.mono_left nhdsWithin_le_nhds
  have hfin := (Real.tendsto_log_atTop.comp hA).atTop_add
    ((tendsto_const_nhds (x := ℓ * Real.log (Real.pi * R ^ 2))).sub hB)
  refine hfin.congr' (Eventually.of_forall fun y => ?_)
  simp only [Function.comp, Pi.add_apply]
  unfold lowerGammaBoundaryLog
  ring

