-- Prove2me | solution 1 for FirstPassageLinearTransport.RecertificationRun.elapsed_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:01.659803+00:00
-- url     : https://prove2.me/submissions/0d89e968-021a-4648-8f9c-4f34a1dc2fb1

import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
import Theorems.Thm_FirstPassageLinearTransport_stageLength_pos


set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace RecertificationRun
theorem _root_.solution
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta} {n elapsed q : ℕ}
    (hrun : RecertificationRun p n elapsed q) : 0 < elapsed := by
  cases hrun with
  | @first m hm0 hnShell hnGood =>
      exact stageLength_pos p hm0 hnShell hnGood
  | @next elapsed qprev m hrun hm0 hsourceShell hsourceGood =>
      have hstage := stageLength_pos p hm0 hsourceShell hsourceGood
      omega
end RecertificationRun
end FirstPassageLinearTransport
