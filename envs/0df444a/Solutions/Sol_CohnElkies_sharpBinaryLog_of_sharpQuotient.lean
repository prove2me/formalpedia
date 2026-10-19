-- Prove2me | solution 1 for CohnElkies.sharpBinaryLog_of_sharpQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/300b73f8-b668-4cde-a90c-22fb47920127

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_log_criticalPackingBase
import Theorems.Thm_CohnElkies_logb_criticalPackingBase
import Theorems.Thm_CohnElkies_sharpLog_of_sharpQuotient

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (hquotient : SharpQuotientAsymptotic) :
    SharpBinaryLogAsymptotic := by
  have hnatural := sharpLog_of_sharpQuotient hquotient
  unfold SharpLogAsymptotic at hnatural
  have hscaled := hnatural.div_const (Real.log 2)
  have hconstant :
      ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi))) /
          Real.log 2 = -criticalBinaryExponent := by
    calc
      _ = Real.log criticalPackingBase / Real.log 2 := by
        rw [log_criticalPackingBase]
      _ = Real.logb 2 criticalPackingBase := by
        rfl
      _ = -criticalBinaryExponent := logb_criticalPackingBase
  rw [hconstant] at hscaled
  unfold SharpBinaryLogAsymptotic
  refine hscaled.congr' (Filter.Eventually.of_forall ?_)
  intro d
  change
    (Real.log (linearProgram d) / (d : ℝ)) / Real.log 2 =
      (Real.log (linearProgram d) / Real.log 2) / (d : ℝ)
  ring
end CohnElkies
