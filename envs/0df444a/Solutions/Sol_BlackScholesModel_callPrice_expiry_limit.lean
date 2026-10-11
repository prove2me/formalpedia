-- Prove2me | solution 1 for BlackScholesModel.callPrice_expiry_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T15:56:54.031821+00:00
-- url     : https://prove2.me/submissions/2f9934a8-a0e2-48ee-98cd-035c9c6fe569

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_dPlus_expiry_tail_limits
import Theorems.Thm_BlackScholesModel_callPrice_expiry_at_strike
import Theorems.Thm_BlackScholesModel_stdNormalCDF_tail_limits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- The terminal call payoff follows by the three moneyness cases. -/
theorem solution (K r σ T S : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (hS : 0 < S) :
    Tendsto (fun t => callPrice K r σ T S t) (𝓝[<] T)
      (𝓝 (max (S - K) 0)) := by
  have hroot : Tendsto (fun t : ℝ => Real.sqrt (T - t))
      (𝓝[<] T) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Real.sqrt (T - t)) := by
      fun_prop
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;>
      simp
  have hshift : Tendsto (fun t : ℝ => -(σ * Real.sqrt (T - t)))
      (𝓝[<] T) (𝓝 0) := by
    simpa only [mul_zero, neg_zero] using
      (tendsto_const_nhds.mul hroot).neg
  have hdisc : Tendsto (fun t : ℝ => Real.exp (-r * (T - t)))
      (𝓝[<] T) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (-r * (T - t))) := by
      fun_prop
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;>
      simp
  rcases lt_trichotomy S K with hless | hequal | hgreater
  · have hp := (dPlus_expiry_tail_limits K r σ T S hK hσ hS).2 hless
    have hm : Tendsto (fun t : ℝ => dMinus S K r σ (T - t))
        (𝓝[<] T) atBot := by
      convert hp.atBot_add hshift using 1 <;>
        first
        | rfl
        | (funext t; dsimp [dMinus, sub_eq_add_neg])
    have hnp : Tendsto (fun t : ℝ => stdNormalCDF (dPlus S K r σ (T - t)))
        (𝓝[<] T) (𝓝 0) := stdNormalCDF_tail_limits.1.comp hp
    have hnm : Tendsto (fun t : ℝ => stdNormalCDF (dMinus S K r σ (T - t)))
        (𝓝[<] T) (𝓝 0) := stdNormalCDF_tail_limits.1.comp hm
    have hprice := (hnp.mul_const S).sub ((hnm.mul_const K).mul hdisc)
    have hmax : max (S - K) 0 = 0 := max_eq_right (sub_nonpos.mpr (le_of_lt hless))
    rw [hmax]
    convert hprice using 1 <;>
      first
      | rfl
      | (funext t; simp only [callPrice]; ring)
      | ring
  · subst S
    simpa using callPrice_expiry_at_strike K r σ T hK hσ
  · have hp := (dPlus_expiry_tail_limits K r σ T S hK hσ hS).1 hgreater
    have hm : Tendsto (fun t : ℝ => dMinus S K r σ (T - t))
        (𝓝[<] T) atTop := by
      convert hp.atTop_add hshift using 1 <;>
        first
        | rfl
        | (funext t; dsimp [dMinus, sub_eq_add_neg])
    have hnp : Tendsto (fun t : ℝ => stdNormalCDF (dPlus S K r σ (T - t)))
        (𝓝[<] T) (𝓝 1) := stdNormalCDF_tail_limits.2.comp hp
    have hnm : Tendsto (fun t : ℝ => stdNormalCDF (dMinus S K r σ (T - t)))
        (𝓝[<] T) (𝓝 1) := stdNormalCDF_tail_limits.2.comp hm
    have hprice := (hnp.mul_const S).sub ((hnm.mul_const K).mul hdisc)
    have hmax : max (S - K) 0 = S - K := max_eq_left (sub_nonneg.mpr (le_of_lt hgreater))
    rw [hmax]
    convert hprice using 1 <;>
      first
      | rfl
      | (funext t; simp only [callPrice]; ring)
      | ring
