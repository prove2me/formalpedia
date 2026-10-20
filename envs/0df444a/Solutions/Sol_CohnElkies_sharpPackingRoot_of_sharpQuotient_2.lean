-- Prove2me | solution 2 for CohnElkies.sharpPackingRoot_of_sharpQuotient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:24:45.959746+00:00
-- url     : https://prove2.me/submissions/91b80db3-152b-42be-92cc-d95d072231f2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_packingGeometricRoot
import Theorems.Thm_CohnElkies_linearProgram_root_eq_geometric_mul_normalizedProgram_unconditional
import Theorems.Thm_CohnElkies_eventually_linearProgram_pos_of_sharpQuotient
import Theorems.Thm_CohnElkies_log_criticalPackingBase
import Theorems.Thm_CohnElkies_logb_criticalPackingBase
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
theorem h47_root (hquotient : CohnElkies.SharpQuotientAsymptotic) :
    Tendsto (fun d : ℕ => (CohnElkies.linearProgram d) ^ ((d : ℝ)⁻¹)) atTop
      (nhds CohnElkies.criticalPackingBase) := by
  have hq : Tendsto CohnElkies.normalizedProgram atTop (nhds CohnElkies.criticalRadius) := hquotient
  have h := CohnElkies.tendsto_packingGeometricRoot.mul hq
  have hX : 0 ≤ Real.sqrt (2 * Real.pi * Real.exp 1) / 2 * CohnElkies.criticalRadius := by
    unfold CohnElkies.criticalRadius; have := Real.pi_pos; positivity
  have key : (Real.sqrt (2 * Real.pi * Real.exp 1) / 2 * CohnElkies.criticalRadius) ^ 2 =
      Real.exp 1 / (2 * Real.pi) := by
    unfold CohnElkies.criticalRadius
    have hp := Real.pi_pos
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hval : Real.sqrt (2 * Real.pi * Real.exp 1) / 2 * CohnElkies.criticalRadius =
      CohnElkies.criticalPackingBase := by
    unfold CohnElkies.criticalPackingBase
    rw [← key, Real.sqrt_sq hX]
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with d hd
  rw [CohnElkies.linearProgram_root_eq_geometric_mul_normalizedProgram_unconditional hd]

theorem h47_logroot (hquotient : CohnElkies.SharpQuotientAsymptotic) :
    Tendsto (fun d : ℕ => Real.log (CohnElkies.linearProgram d) / (d : ℝ)) atTop
      (nhds (Real.log CohnElkies.criticalPackingBase)) := by
  have hc : 0 < CohnElkies.criticalPackingBase := by
    unfold CohnElkies.criticalPackingBase
    exact Real.sqrt_pos.mpr (by have := Real.pi_pos; positivity)
  have h := ((Real.continuousAt_log hc.ne').tendsto).comp (h47_root hquotient)
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0,
    CohnElkies.eventually_linearProgram_pos_of_sharpQuotient hquotient] with d hd hpos
  simp only [Function.comp]
  rw [Real.log_rpow hpos]
  field_simp

theorem solution
    (hquotient : SharpQuotientAsymptotic) :
    SharpPackingRootAsymptotic := by
  exact h47_root hquotient

