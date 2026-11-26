-- Prove2me | solution 1 for FirstPassageLinearTransport.CertifiedRankChain.directFirstPassage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:03.760805+00:00
-- url     : https://prove2.me/submissions/19af43fd-b6e2-46c1-b68c-9dd15432a676

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Theorems.Thm_FirstPassageLinearTransport_IsFirstPassage_nested


set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace CertifiedRankChain
theorem _root_.solution
    {r : ℚ} {n t q : ℕ} (hchain : CertifiedRankChain r n t q) :
    IsFirstPassage (2 ^ q) n t := by
  induction hchain with
  | first hfp _hhm _hm => exact hfp
  | @next t qprev q m h hchain hgap hfp hhm hm ih =>
      have hthreshold : 2 ^ q < 2 ^ qprev :=
        Nat.pow_lt_pow_right (by omega) hgap
      exact ih.nested hthreshold hfp
end CertifiedRankChain
end FirstPassageLinearTransport
