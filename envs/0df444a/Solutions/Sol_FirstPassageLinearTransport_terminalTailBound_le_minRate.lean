-- Prove2me | solution 1 for FirstPassageLinearTransport.terminalTailBound_le_minRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:06.11713+00:00
-- url     : https://prove2.me/submissions/f68ac7f6-437b-486b-b60b-3f8552d36373

import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
import Theorems.Thm_FirstPassageLinearTransport_weightedTailConstant_pos

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {b b' c' : ℝ}
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (L : ℕ) :
    terminalTailBound b b' c' L ≤
      terminalTailPrefactor b b' c' *
        Real.exp (-(min b' c' * (L : ℝ))) := by
  have hdy0 : 0 ≤ weightedTailConstant (Real.log 2) c' :=
    (weightedTailConstant_pos hc' hc2).le
  have hent0 : 0 ≤ Real.exp b * weightedTailConstant b b' := by
    exact mul_nonneg (Real.exp_pos b).le
      (weightedTailConstant_pos hb' hbb').le
  have hL0 : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hdyExp :
      Real.exp (-(c' * (L : ℝ))) ≤
        Real.exp (-(min b' c' * (L : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hmin := min_le_right b' c'
    nlinarith
  have hentExp :
      Real.exp (-(b' * (L : ℝ))) ≤
        Real.exp (-(min b' c' * (L : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hmin := min_le_left b' c'
    nlinarith
  unfold terminalTailBound terminalTailPrefactor
  calc
    weightedTailConstant (Real.log 2) c' *
          Real.exp (-(c' * (L : ℝ))) +
        Real.exp b * weightedTailConstant b b' *
          Real.exp (-(b' * (L : ℝ))) ≤
      weightedTailConstant (Real.log 2) c' *
          Real.exp (-(min b' c' * (L : ℝ))) +
        Real.exp b * weightedTailConstant b b' *
          Real.exp (-(min b' c' * (L : ℝ))) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hdyExp hdy0)
        (mul_le_mul_of_nonneg_left hentExp hent0)
    _ = (weightedTailConstant (Real.log 2) c' +
          Real.exp b * weightedTailConstant b b') *
        Real.exp (-(min b' c' * (L : ℝ))) := by ring
end FirstPassageLinearTransport
