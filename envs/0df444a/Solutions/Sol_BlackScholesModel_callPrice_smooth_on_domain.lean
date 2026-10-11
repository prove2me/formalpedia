-- Prove2me | solution 1 for BlackScholesModel.callPrice_smooth_on_domain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T15:41:54.016716+00:00
-- url     : https://prove2.me/submissions/a87075d6-9a34-46e8-a46b-01a55bd9a257

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_stdNormalCDF_contDiff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Smoothness on the positive-spot, pre-expiry Black-Scholes domain. -/
theorem solution (K r σ T : ℝ) (hK : 0 < K) (hσ : 0 < σ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => callPrice K r σ T p.1 p.2)
        {p : ℝ × ℝ | 0 < p.1 ∧ p.2 < T} := by
  intro p hp
  have hS : 0 < p.1 := hp.1
  have hτ : 0 < T - p.2 := sub_pos.mpr hp.2
  have hdiv0 : p.1 / K ≠ 0 :=
    ne_of_gt (div_pos hS hK)
  have hsqrt0 : Real.sqrt (T - p.2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hτ)
  have hden0 : σ * Real.sqrt (T - p.2) ≠ 0 :=
    mul_ne_zero (ne_of_gt hσ) hsqrt0
  have hratio : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => q.1 / K) p := by
    fun_prop
  have hlog : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => Real.log (q.1 / K)) p :=
    hratio.log hdiv0
  have htau : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => T - q.2) p := by
    fun_prop
  have hsqrt : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => Real.sqrt (T - q.2)) p :=
    htau.sqrt (ne_of_gt hτ)
  have hnum : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ =>
        Real.log (q.1 / K) + (r + σ ^ 2 / 2) * (T - q.2)) p := by
    convert hlog.add ((contDiffAt_const.mul htau)) using 1 <;>
      first
      | rfl
      | (funext q; ring)
  have hden : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => σ * Real.sqrt (T - q.2)) p :=
    contDiffAt_const.mul hsqrt
  have hdplus : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => dPlus q.1 K r σ (T - q.2)) p := by
    convert hnum.div hden hden0 using 1 <;>
      first
      | rfl
      | (funext q; rfl)
  have hdminus : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => dMinus q.1 K r σ (T - q.2)) p := by
    convert hdplus.sub (contDiffAt_const.mul hsqrt) using 1 <;>
      first
      | rfl
      | (funext q; rfl)
  have hcdf : ContDiff ℝ ∞ stdNormalCDF :=
    stdNormalCDF_contDiff
  have hcplus : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ =>
        stdNormalCDF (dPlus q.1 K r σ (T - q.2))) p := by
    simpa only [Function.comp_def] using hcdf.contDiffAt.comp p hdplus
  have hcminus : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ =>
        stdNormalCDF (dMinus q.1 K r σ (T - q.2))) p := by
    simpa only [Function.comp_def] using hcdf.contDiffAt.comp p hdminus
  have hspot : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => q.1) p := by
    fun_prop
  have hdiscount : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => Real.exp (-r * (T - q.2))) p := by
    fun_prop
  have hprice : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => callPrice K r σ T q.1 q.2) p := by
    convert (hcplus.mul hspot).sub
      ((hcminus.mul (contDiffAt_const)).mul hdiscount) using 1 <;>
        first
        | rfl
        | (funext q; simp only [callPrice]; ring)
  exact hprice.contDiffWithinAt