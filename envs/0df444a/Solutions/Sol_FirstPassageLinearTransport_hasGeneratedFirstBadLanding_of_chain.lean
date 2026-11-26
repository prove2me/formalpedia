-- Prove2me | solution 1 for FirstPassageLinearTransport.hasGeneratedFirstBadLanding_of_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:42.154255+00:00
-- url     : https://prove2.me/submissions/87c80306-dc90-40e0-ba8c-2baed701bb47

import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_RecertificationStep

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r : ℚ} {t : ℝ} {n h q L U H : ℕ}
    (hLq : L ≤ q) (hqU : q ≤ U) (hh1 : 1 ≤ h) (hhH : h ≤ H)
    (hchain : CertifiedRankChain r n h q)
    (hbad : orbit h n ∈ landingBad q t) :
    HasGeneratedFirstBadLanding r t n L U H :=
  ⟨h, q, hLq, hqU, hh1, hhH, hchain, hbad⟩
end FirstPassageLinearTransport
