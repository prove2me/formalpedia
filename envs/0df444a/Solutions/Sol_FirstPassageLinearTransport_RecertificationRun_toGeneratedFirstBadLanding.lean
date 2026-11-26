-- Prove2me | solution 1 for FirstPassageLinearTransport.RecertificationRun.toGeneratedFirstBadLanding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:48.985244+00:00
-- url     : https://prove2.me/submissions/4a79c11c-f984-4fd8-884c-14ae912e64db

import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_toCertifiedRankChain
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_endpoint_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_hasGeneratedFirstBadLanding_of_chain


set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace RecertificationRun
theorem _root_.solution
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta}
    {n elapsed q L U H : ℕ}
    (hrun : RecertificationRun p n elapsed q)
    (hLq : L ≤ q) (hqU : q ≤ U) (hhH : elapsed ≤ H)
    (hbad : orbit elapsed n ∉ initialWindowGood eta) :
    HasGeneratedFirstBadLanding r eta n L U H :=
  hasGeneratedFirstBadLanding_of_chain hLq hqU hrun.elapsed_pos hhH
    hrun.toCertifiedRankChain (hrun.endpoint_mem_landingBad hbad)
end RecertificationRun
end FirstPassageLinearTransport
