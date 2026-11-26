-- Prove2me | solution 1 for FirstPassageLinearTransport.terminalTailPrefactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:53.946177+00:00
-- url     : https://prove2.me/submissions/d392e48d-dc40-4c13-8e88-5e238ffb6efc

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
    (hc' : 0 < c') (hc2 : c' < Real.log 2) :
    0 < terminalTailPrefactor b b' c' := by
  unfold terminalTailPrefactor
  have hdy := weightedTailConstant_pos hc' hc2
  have hent := weightedTailConstant_pos hb' hbb'
  positivity
end FirstPassageLinearTransport
