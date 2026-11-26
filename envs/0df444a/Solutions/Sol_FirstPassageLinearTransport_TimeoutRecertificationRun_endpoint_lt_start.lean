-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.endpoint_lt_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:01.205692+00:00
-- url     : https://prove2.me/submissions/c1162be7-07de-493e-adab-f637ceada141

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_currentRank_lt_startShell
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hnShell : n ∈ dyadicShell M) : orbit elapsed n < n := by
  have hqM := hrun.currentRank_lt_startShell
  exact hrun.directFirstPassage.1.trans_lt
    ((Nat.pow_lt_pow_right (by omega) hqM).trans_le
      (mem_dyadicShell.mp hnShell).1)
end TimeoutRecertificationRun
end FirstPassageLinearTransport
