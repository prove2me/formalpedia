-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_m17_closedcap_real_horizon_masked_rate_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:38:54.407904+00:00
-- url     : https://prove2.me/submissions/8d4da7a3-3c65-4a6d-8e7a-1fe5cc46fb03

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Defs.Filter
import Theorems.Thm_AvramDividend_Classical_avram_bva21_closed_cap_continuous_kernel_mask_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C τ : ℝ≥0∞) (q T a : ℝ)
    (U : ℝ≥0 → ℝ) (hU : Measurable U)
    (ψ : ℝ → ℝ)
    (hψ : ContinuousOn ψ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ (t : ℝ) < a ∧
          (t : ℝ≥0∞) ≤ τ ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then Real.exp (-(q * (t : ℝ))) * ψ (U t) else 0) := by
  have hmasked :
      Measurable (fun t : ℝ≥0 =>
        if 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then ψ (U t) else 0) :=
    avram_bva21_closed_cap_continuous_kernel_mask_measurable C ψ hψ U hU
  have hclock : MeasurableSet
      {t : ℝ≥0 | 0 < t ∧ (t : ℝ) < a ∧ (t : ℝ≥0∞) ≤ τ} := by
    measurability
  have hexp : Measurable (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ)))) := by
    fun_prop
  have hcombined : Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ (t : ℝ) < a ∧ (t : ℝ≥0∞) ≤ τ then
        Real.exp (-(q * (t : ℝ))) *
          (if 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then ψ (U t) else 0)
      else 0) :=
    (hexp.mul hmasked).ite hclock measurable_const
  convert hcombined using 1
  funext t
  by_cases hc : 0 < t ∧ (t : ℝ) < a ∧ (t : ℝ≥0∞) ≤ τ
  · by_cases hb : 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
    · simp [hc.1, hc.2.1, hc.2.2, hb.1, hb.2]
    · simp [hc.1, hc.2.1, hc.2.2, hb]
  · simp only [not_and_or] at hc
    rcases hc with hc | hc | hc
    · simp [hc]
    · simp [hc]
    · simp [hc]
