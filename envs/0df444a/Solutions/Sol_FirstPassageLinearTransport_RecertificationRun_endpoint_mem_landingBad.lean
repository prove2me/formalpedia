-- Prove2me | solution 1 for FirstPassageLinearTransport.RecertificationRun.endpoint_mem_landingBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:23.767678+00:00
-- url     : https://prove2.me/submissions/37519988-82c1-4b5b-a448-97246649dfc2

import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_currentRank_pos
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_toCertifiedRankChain
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_firstPassage_band
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_landingBad



set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace RecertificationRun
theorem _root_.solution
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta} {n elapsed q : ℕ}
    (hrun : RecertificationRun p n elapsed q)
    (hbad : orbit elapsed n ∉ initialWindowGood eta) :
    orbit elapsed n ∈ landingBad q eta := by
  have hchain := hrun.toCertifiedRankChain
  have hfp := hchain.directFirstPassage
  have htime := hrun.elapsed_pos
  have hband := firstPassage_band htime hfp
  have hq := hrun.currentRank_pos
  apply mem_landingBad.mpr
  refine ⟨?_, hband.2, hbad⟩
  rw [show q = (q - 1) + 1 by omega, pow_succ] at hband
  omega
end RecertificationRun
end FirstPassageLinearTransport
