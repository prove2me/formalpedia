-- Prove2me | solution 1 for CarneiroDeSitter.dust_phase_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:52:36.272091+00:00
-- url     : https://prove2.me/submissions/db933749-e50f-45d9-a681-cd46090c9074

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set
namespace CarneiroDeSitter

lemma da_H (C σ : ℝ) (hC : 0 < C) (hσ : 0 < σ) (s : ℝ) (hs : 0 < s) :
    deriv (dustScaleFactor C σ) s / dustScaleFactor C σ s
      = σ / 3 * Real.exp (σ * s / 2) / (Real.exp (σ * s / 2) - 1) := by
  have hE : 0 < Real.exp (σ * s / 2) - 1 := by
    have : 1 < Real.exp (σ * s / 2) := Real.one_lt_exp_iff.2 (by positivity)
    linarith
  have h1 : HasDerivAt (fun s => Real.exp (σ * s / 2) - 1) (Real.exp (σ * s / 2) * (σ / 2)) s := by
    have : HasDerivAt (fun s => σ * s / 2) (σ / 2) s := by
      simpa using ((hasDerivAt_id s).const_mul σ).div_const 2
    exact (this.exp).sub_const 1
  have h2 := h1.rpow_const (p := (2:ℝ)/3) (Or.inl hE.ne')
  have h3 : HasDerivAt (dustScaleFactor C σ) _ s := h2.const_mul C
  rw [h3.deriv, dustScaleFactor]
  have : (Real.exp (σ * s / 2) - 1) ^ ((2:ℝ)/3 - 1)
      = (Real.exp (σ * s / 2) - 1) ^ ((2:ℝ)/3) / (Real.exp (σ * s / 2) - 1) := by
    rw [Real.rpow_sub hE, Real.rpow_one]
  rw [this]
  have hp : 0 < (Real.exp (σ * s / 2) - 1) ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos hE _
  field_simp

theorem dpa (C σ : ℝ) (hC : 0 < C) (hσ : 0 < σ) :
    dustScaleFactor C σ ~[𝓝[>] 0] (fun t => C * (σ / 2) ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3)) ∧
    Tendsto (fun t => deriv (dustScaleFactor C σ) t / dustScaleFactor C σ t) atTop
      (𝓝 (σ / 3)) := by
  constructor
  · apply isEquivalent_of_tendsto_one
    -- slope of exp(σx/2) at 0
    have hd : HasDerivAt (fun x => Real.exp (σ * x / 2)) (Real.exp (σ * 0 / 2) * (σ / 2)) 0 := by
      have : HasDerivAt (fun s => σ * s / 2) (σ / 2) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).const_mul σ).div_const 2
      exact this.exp
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    simp only [zero_add, mul_zero, zero_div, Real.exp_zero, one_mul, smul_eq_mul] at hd
    have hq : Tendsto (fun t => (t⁻¹ * (Real.exp (σ * t / 2) - 1)) / (σ / 2)) (𝓝[>] 0) (𝓝 1) := by
      have := (hd.mono_left (nhdsGT_le_nhdsNE 0)).div_const (σ / 2)
      rwa [div_self (by positivity)] at this
    have hr := hq.rpow_const (p := (2:ℝ)/3) (Or.inl one_ne_zero)
    rw [Real.one_rpow] at hr
    apply hr.congr'
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hE : 0 < Real.exp (σ * t / 2) - 1 := by
      have : 1 < Real.exp (σ * t / 2) := Real.one_lt_exp_iff.2 (by positivity)
      linarith
    simp only [Pi.div_apply, dustScaleFactor]
    have e : t⁻¹ * (Real.exp (σ * t / 2) - 1) / (σ / 2) = (Real.exp (σ * t / 2) - 1) / ((σ / 2) * t) := by
      field_simp
    rw [e, Real.div_rpow hE.le (by positivity), Real.mul_rpow (by positivity) ht.le]
    have h1 : 0 < (σ / 2) ^ ((2:ℝ)/3) := by positivity
    have h2 : 0 < t ^ ((2:ℝ)/3) := by positivity
    field_simp
  · have hlim : Tendsto (fun t => σ / 3 / (1 - Real.exp (-(σ / 2 * t)))) atTop (𝓝 (σ / 3 / (1 - 0))) := by
      apply Tendsto.div tendsto_const_nhds _ (by norm_num)
      apply tendsto_const_nhds.sub
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by positivity))
    rw [sub_zero, div_one] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [da_H C σ hC hσ t ht]
    have hE : 0 < Real.exp (σ * t / 2) - 1 := by
      have : 1 < Real.exp (σ * t / 2) := Real.one_lt_exp_iff.2 (by positivity)
      linarith
    have : Real.exp (-(σ / 2 * t)) = (Real.exp (σ * t / 2))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [this]
    have hp : 0 < Real.exp (σ * t / 2) := Real.exp_pos _
    field_simp

end CarneiroDeSitter

open Real Filter Topology Asymptotics MeasureTheory Set CarneiroDeSitter

theorem solution (C σ : ℝ) (hC : 0 < C) (hσ : 0 < σ) :
    dustScaleFactor C σ ~[𝓝[>] 0] (fun t => C * (σ / 2) ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3)) ∧
    Tendsto (fun t => deriv (dustScaleFactor C σ) t / dustScaleFactor C σ t) atTop
      (𝓝 (σ / 3)) := dpa C σ hC hσ
