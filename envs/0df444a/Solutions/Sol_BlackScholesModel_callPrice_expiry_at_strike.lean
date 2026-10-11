-- Prove2me | solution 1 for BlackScholesModel.callPrice_expiry_at_strike
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T16:06:56.272836+00:00
-- url     : https://prove2.me/submissions/2e5d6f25-8422-4fc4-91fe-d130a3476af8

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_stdNormalCDF_contDiff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- The at-the-money call approaches its zero expiry payoff. -/
theorem solution (K r σ T : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) :
    Tendsto (fun t => callPrice K r σ T K t) (𝓝[<] T) (𝓝 0) := by
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (T - t))
      (𝓝[<] T) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Real.sqrt (T - t)) := by
      fun_prop
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;>
      simp
  have hplusEq : (fun t : ℝ => dPlus K K r σ (T - t)) =ᶠ[𝓝[<] T]
      (fun t => ((r + σ ^ 2 / 2) / σ) * Real.sqrt (T - t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hτ : 0 < T - t := sub_pos.mpr ht
    have hroot0 : Real.sqrt (T - t) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hτ)
    have hσ0 : σ ≠ 0 := ne_of_gt hσ
    have hsq : Real.sqrt (T - t) ^ 2 = T - t :=
      Real.sq_sqrt (le_of_lt hτ)
    unfold dPlus
    rw [div_self (ne_of_gt hK), Real.log_one, zero_add]
    calc
      ((r + σ ^ 2 / 2) * (T - t)) /
          (σ * Real.sqrt (T - t)) =
        ((r + σ ^ 2 / 2) * Real.sqrt (T - t) ^ 2) /
          (σ * Real.sqrt (T - t)) := by rw [hsq]
      _ = ((r + σ ^ 2 / 2) / σ) * Real.sqrt (T - t) := by
        field_simp [hσ0, hroot0]
  have hplus : Tendsto (fun t : ℝ => dPlus K K r σ (T - t))
      (𝓝[<] T) (𝓝 0) := by
    have hh : Tendsto
        (fun t : ℝ => ((r + σ ^ 2 / 2) / σ) * Real.sqrt (T - t))
        (𝓝[<] T) (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hsqrt)
    exact hh.congr' hplusEq.symm
  have hminus : Tendsto (fun t : ℝ => dMinus K K r σ (T - t))
      (𝓝[<] T) (𝓝 0) := by
    have hσroot : Tendsto (fun t : ℝ => σ * Real.sqrt (T - t))
        (𝓝[<] T) (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => σ)
          (𝓝[<] T) (𝓝 σ)).mul hsqrt
    have hsub := hplus.sub hσroot
    convert hsub using 1 <;>
      first
      | rfl
      | (funext t; simp only [dMinus])
      | ring
  have hcont : Continuous stdNormalCDF :=
    stdNormalCDF_contDiff.continuous
  have hNplus : Tendsto
      (fun t : ℝ => stdNormalCDF (dPlus K K r σ (T - t)))
      (𝓝[<] T) (𝓝 (stdNormalCDF 0)) :=
    hcont.continuousAt.tendsto.comp hplus
  have hNminus : Tendsto
      (fun t : ℝ => stdNormalCDF (dMinus K K r σ (T - t)))
      (𝓝[<] T) (𝓝 (stdNormalCDF 0)) :=
    hcont.continuousAt.tendsto.comp hminus
  have hdiscount : Tendsto
      (fun t : ℝ => Real.exp (-r * (T - t))) (𝓝[<] T) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (-r * (T - t))) := by
      fun_prop
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;>
      simp
  have hprice := (hNplus.mul_const K).sub
    ((hNminus.mul_const K).mul hdiscount)
  convert hprice using 1 <;>
    first
    | rfl
    | (funext t; simp only [callPrice]; ring)
    | ring