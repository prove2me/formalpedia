-- Prove2me | solution 1 for Formalism.SLP.P.two_pow_length_primeFactorsList_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:27.033101+00:00
-- url     : https://prove2.me/submissions/76763389-e9d3-41ec-9355-0fd2f1cc65ce

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_OmegaPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.P
namespace Formalism.SLP.P
theorem _root_.solution (j : ℕ) (hj : 1 ≤ j) :
    2 ^ (Nat.primeFactorsList j).length ≤ j := by
  have hprod := Nat.prod_primeFactorsList (show j ≠ 0 by omega)
  calc 2 ^ (Nat.primeFactorsList j).length ≤ (Nat.primeFactorsList j).prod :=
        List.pow_card_le_prod _ _ (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
    _ = j := hprod
end Formalism.SLP.P
