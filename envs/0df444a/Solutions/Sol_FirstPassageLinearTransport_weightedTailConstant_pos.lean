-- Prove2me | solution 1 for FirstPassageLinearTransport.weightedTailConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:02.477812+00:00
-- url     : https://prove2.me/submissions/7f41d074-1ea5-4215-a642-ffd65dac9316

import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {c c' : ℝ} (hc' : 0 < c') (hcc' : c' < c) :
    0 < weightedTailConstant c c' := by
  unfold weightedTailConstant
  have hgap : 0 < c - c' := sub_pos.mpr hcc'
  have hexp : Real.exp (-c') < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hnum : 0 < 1 + 1 / (c - c') := by positivity
  have hden : 0 < 1 - Real.exp (-c') := sub_pos.mpr hexp
  exact div_pos hnum hden
end FirstPassageLinearTransport
