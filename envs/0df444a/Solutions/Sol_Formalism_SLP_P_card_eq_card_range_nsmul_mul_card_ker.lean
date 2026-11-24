-- Prove2me | solution 1 for Formalism.SLP.P.card_eq_card_range_nsmul_mul_card_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:20.71928+00:00
-- url     : https://prove2.me/submissions/7c8a9f71-64a5-4407-9e97-52b7f409922d

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CardEqCardRangeNsmulMulCardKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.SLP Formalism.SLP.P
namespace Formalism.SLP.P
theorem _root_.solution : Formalism.SLP.TorsionIndexEq := by
  intro A _ _ g
  set f : A →+ A := nsmulAddMonoidHom g
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
end Formalism.SLP.P
