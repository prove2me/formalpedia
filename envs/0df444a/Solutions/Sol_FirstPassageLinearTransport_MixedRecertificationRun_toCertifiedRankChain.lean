-- Prove2me | solution 1 for FirstPassageLinearTransport.MixedRecertificationRun.toCertifiedRankChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:04.074469+00:00
-- url     : https://prove2.me/submissions/e253a3f2-4f58-49cb-81ca-e80009310967

import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_first_of_stage_common
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_next_of_stage_common

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace MixedRecertificationRun
theorem _root_.solution
    {rStar : ℚ} (hrStar : 0 < rStar) {n elapsed q : ℕ}
    (hrun : MixedRecertificationRun rStar n elapsed q) :
    CertifiedRankChain rStar n elapsed q := by
  induction hrun with
  | first p hStar hm0 hnShell hnGood =>
      exact CertifiedRankChain.first_of_stage_common
        p hrStar hStar hm0 hnShell hnGood
  | next hrun p hStar hm0 hsourceShell hsourceGood hgap ih =>
      exact CertifiedRankChain.next_of_stage_common
        p hrStar hStar ih hm0 hsourceShell hsourceGood hgap
end MixedRecertificationRun
end FirstPassageLinearTransport
