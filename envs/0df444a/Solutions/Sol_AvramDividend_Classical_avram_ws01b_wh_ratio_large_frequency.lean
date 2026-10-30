-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_wh_ratio_large_frequency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:25:40.462983+00:00
-- url     : https://prove2.me/submissions/91c82f4a-61e5-4bec-bd23-580e07f42306

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal ENNReal

/-- BV drift asymptotics give the exact large-frequency WH quotient
needed to identify the genuine original exponential-clock drawdown atom. -/
theorem solution (ψ : ℝ → ℝ) (R φ d : ℝ)
    (hφ : 0 < φ) (hd : 0 < d)
    (hSlope : Tendsto (fun t : ℝ => (d * t - ψ t) / t)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun t : ℝ => (R / φ) * ((φ - t) / (R - ψ t)))
      atTop (𝓝 (R / (φ * d))) := by
  have hInv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hPsi : Tendsto (fun t : ℝ => ψ t / t) atTop (𝓝 d) := by
    have hDiff : Tendsto
        (fun t : ℝ => d - ((d * t - ψ t) / t))
        atTop (𝓝 (d - (0 : ℝ))) :=
      tendsto_const_nhds.sub hSlope
    have hEq : (fun t : ℝ => d - ((d * t - ψ t) / t)) =ᶠ[atTop]
        (fun t : ℝ => ψ t / t) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have ht0 : t ≠ 0 := ne_of_gt ht
      field_simp [ht0]
      ring
    simpa using hDiff.congr' hEq
  have hφDiv : Tendsto (fun t : ℝ => φ / t) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hInv :
        Tendsto (fun t : ℝ => φ * t⁻¹) atTop (𝓝 (φ * (0 : ℝ))))
  have hRDiv : Tendsto (fun t : ℝ => R / t) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hInv :
        Tendsto (fun t : ℝ => R * t⁻¹) atTop (𝓝 (R * (0 : ℝ))))
  have hNum : Tendsto (fun t : ℝ => φ / t - 1)
      atTop (𝓝 (-1 : ℝ)) := by
    convert hφDiv.sub tendsto_const_nhds using 1 <;> norm_num
  have hDen : Tendsto (fun t : ℝ => R / t - ψ t / t)
      atTop (𝓝 (-d : ℝ)) := by
    convert hRDiv.sub hPsi using 1 <;> ring
  have hd0 : (-d : ℝ) ≠ 0 := neg_ne_zero.mpr (ne_of_gt hd)
  have hQuot : Tendsto
      (fun t : ℝ => (φ / t - 1) / (R / t - ψ t / t))
      atTop (𝓝 ((-1 : ℝ) / (-d))) :=
    hNum.div hDen hd0
  have hMul : Tendsto
      (fun t : ℝ => (R / φ) * ((φ / t - 1) / (R / t - ψ t / t)))
      atTop (𝓝 ((R / φ) * ((-1 : ℝ) / (-d)))) :=
    tendsto_const_nhds.mul hQuot
  have hEq : (fun t : ℝ =>
      (R / φ) * ((φ / t - 1) / (R / t - ψ t / t))) =ᶠ[atTop]
      (fun t : ℝ => (R / φ) * ((φ - t) / (R - ψ t))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    by_cases hb : R - ψ t = 0
    · have hb' : R / t - ψ t / t = 0 := by
        rw [← sub_div, hb, zero_div]
      simp [hb, hb']
    · have hb' : R / t - ψ t / t ≠ 0 := by
        rw [← sub_div]
        exact div_ne_zero hb ht0
      field_simp [ht0, hb, hb']
  have hLimit : (R / φ) * ((-1 : ℝ) / (-d)) =
      R / (φ * d) := by
    field_simp [ne_of_gt hφ, ne_of_gt hd]
  simpa only [hLimit] using hMul.congr' hEq
