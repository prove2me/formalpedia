-- Prove2me | solution 1 for FirstPassageLinearTransport.initialWindowGood_powerDense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:16.232526+00:00
-- url     : https://prove2.me/submissions/5afefc0f-8eed-4710-ac3d-055c7923ec3c

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_shellBad_initialWindowGood
import Theorems.Thm_FirstPassageLinearTransport_maximalBarrierC0_pos
import Theorems.Thm_FirstPassageLinearTransport_maximalBarrierC0_lt_log_two
import Theorems.Thm_FirstPassageLinearTransport_quadraticWindowShellConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_card_shellInitialWindowBad_le_quadratic
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_powerDense_of_shell_bound
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    PowerDense (initialWindowGood t)
      (quadraticWindowGlobalConstant t)
      (quadraticWindowDensityRate t) := by
  have hc : 0 < maximalBarrierC0 * t ^ 2 :=
    mul_pos maximalBarrierC0_pos (sq_pos_of_pos ht0)
  have hclt : maximalBarrierC0 * t ^ 2 < Real.log 2 := by
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
    have hle : maximalBarrierC0 * t ^ 2 ≤ maximalBarrierC0 :=
      mul_le_of_le_one_right maximalBarrierC0_pos.le ht2
    exact hle.trans_lt maximalBarrierC0_lt_log_two
  unfold quadraticWindowGlobalConstant quadraticWindowDensityRate
  apply powerDense_of_shell_bound
    quadraticWindowShellConstant_pos hc hclt
  intro M
  rw [shellBad_initialWindowGood]
  simpa [mul_assoc] using
    (card_shellInitialWindowBad_le_quadratic (M := M) ht0 ht1)
end FirstPassageLinearTransport
