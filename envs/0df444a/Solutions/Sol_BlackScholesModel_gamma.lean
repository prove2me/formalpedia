-- Prove2me | solution 1 for BlackScholesModel.gamma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T14:21:57.085405+00:00
-- url     : https://prove2.me/submissions/02fb3449-1f90-4d31-8333-95b6b0b91cf6

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_call_delta
import Theorems.Thm_BlackScholesModel_put_delta
import Theorems.Thm_BlackScholesModel_stdNormalCDF_hasDerivAt
import Theorems.Thm_BlackScholesModel_dPlus_hasDerivAt_spot

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (K r σ T S t : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun S' => deriv (fun S'' => callPrice K r σ T S'' t) S')
      (stdNormalPDF (dPlus S K r σ (T - t)) / (S * σ * Real.sqrt (T - t))) S ∧
    HasDerivAt (fun S' => deriv (fun S'' => putPrice K r σ T S'' t) S')
      (stdNormalPDF (dPlus S K r σ (T - t)) / (S * σ * Real.sqrt (T - t))) S := by
  have hs_event : ∀ᶠ s : ℝ in 𝓝 S, 0 < s :=
    eventually_gt_nhds hS
  have hplus := dPlus_hasDerivAt_spot
    S K r σ (T - t) hS hK hσ (sub_pos.mpr ht)
  have houter : HasDerivAt (fun z : ℝ => stdNormalCDF z)
      (stdNormalPDF (dPlus S K r σ (T - t)))
      (dPlus S K r σ (T - t)) :=
    stdNormalCDF_hasDerivAt (dPlus S K r σ (T - t))
  have hN : HasDerivAt
      (fun s : ℝ => stdNormalCDF (dPlus s K r σ (T - t)))
      (stdNormalPDF (dPlus S K r σ (T - t)) *
        (1 / (S * σ * Real.sqrt (T - t)))) S := by
    simpa only [Function.comp_def] using houter.comp S hplus
  have hvalue :
      stdNormalPDF (dPlus S K r σ (T - t)) *
          (1 / (S * σ * Real.sqrt (T - t))) =
        stdNormalPDF (dPlus S K r σ (T - t)) /
          (S * σ * Real.sqrt (T - t)) := by ring
  have hcall_event :
      (fun s : ℝ => deriv (fun u => callPrice K r σ T u t) s) =ᶠ[𝓝 S]
        (fun s : ℝ => stdNormalCDF (dPlus s K r σ (T - t))) := by
    filter_upwards [hs_event] with s hs
    exact (call_delta K r σ T s t hK hσ hs ht).deriv
  have hput_event :
      (fun s : ℝ => deriv (fun u => putPrice K r σ T u t) s) =ᶠ[𝓝 S]
        (fun s : ℝ => stdNormalCDF (dPlus s K r σ (T - t)) - 1) := by
    filter_upwards [hs_event] with s hs
    have hh := put_delta K r σ T s t hK hσ hs ht
    have hderiv := hh.1.deriv
    rw [hh.2] at hderiv
    exact hderiv
  constructor
  · have hh := hN.congr_of_eventuallyEq hcall_event
    rw [hvalue] at hh
    exact hh
  · have hNm1 : HasDerivAt
        (fun s : ℝ => stdNormalCDF (dPlus s K r σ (T - t)) - 1)
        (stdNormalPDF (dPlus S K r σ (T - t)) *
          (1 / (S * σ * Real.sqrt (T - t)))) S := by
      simpa only [sub_eq_add_neg] using hN.add_const (-1)
    have hh := hNm1.congr_of_eventuallyEq hput_event
    rw [hvalue] at hh
    exact hh