-- Prove2me | solution 1 for FirstPassageLinearTransport.terminalTailBound_polylog_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:51.93696+00:00
-- url     : https://prove2.me/submissions/30ac8c06-3fa8-4813-90a3-cdaab8dd4451

import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
import Theorems.Thm_FirstPassageLinearTransport_terminalTailPrefactor_pos
import Theorems.Thm_FirstPassageLinearTransport_terminalTailBound_le_minRate
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_polylogTerminalRank_lower
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A b b' c' : ℝ}
    (_hA : 0 < A)
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (M : ℕ) :
    terminalTailBound b b' c' (polylogTerminalRank A M) ≤
      terminalTailPrefactor b b' c' *
        (((M : ℝ) + 2) ^
          (-(A * min b' c' / Real.log 2))) := by
  let d := min b' c'
  have hd : 0 < d := lt_min hb' hc'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0 < (M : ℝ) + 2 := by positivity
  have hL := polylogTerminalRank_lower A M
  have hscaled :
      d * (A * Real.logb 2 ((M : ℝ) + 2)) ≤
        d * (polylogTerminalRank A M : ℝ) :=
    mul_le_mul_of_nonneg_left hL hd.le
  have hexp :
      Real.exp (-(d * (polylogTerminalRank A M : ℝ))) ≤
        Real.exp (-(d * (A * Real.logb 2 ((M : ℝ) + 2)))) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hpref0 : 0 ≤ terminalTailPrefactor b b' c' :=
    (terminalTailPrefactor_pos hb' hbb' hc' hc2).le
  calc
    terminalTailBound b b' c' (polylogTerminalRank A M) ≤
        terminalTailPrefactor b b' c' *
          Real.exp (-(d * (polylogTerminalRank A M : ℝ))) := by
      simpa [d] using terminalTailBound_le_minRate
        hb' hbb' hc' hc2 (polylogTerminalRank A M)
    _ ≤ terminalTailPrefactor b b' c' *
        Real.exp (-(d * (A * Real.logb 2 ((M : ℝ) + 2)))) :=
      mul_le_mul_of_nonneg_left hexp hpref0
    _ = terminalTailPrefactor b b' c' *
        (((M : ℝ) + 2) ^ (-(A * d / Real.log 2))) := by
      congr 1
      rw [Real.rpow_def_of_pos hx]
      simp only [Real.logb]
      congr 1
      field_simp [ne_of_gt hlog2]
end FirstPassageLinearTransport
