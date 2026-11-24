-- Prove2me | solution 1 for Formalism.SLP.P.card_range_nsmul_mul_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:33.072915+00:00
-- url     : https://prove2.me/submissions/8a7412b3-a027-476d-bc6f-ba1fe051f105

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CardEqCardRangeNsmulMulCardKer
import Theorems.Thm_Formalism_SLP_P_card_eq_card_range_nsmul_mul_card_ker

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
theorem _root_.solution : Formalism.SLP.TorsionIndex := by
  intro A _ _ g K hK
  have hle : K ≤ (nsmulAddMonoidHom g : A →+ A).ker := fun x hx => by
    simpa using hK x hx
  rw [card_eq_card_range_nsmul_mul_card_ker A g]
  exact Nat.mul_le_mul_left _ (AddSubgroup.card_le_of_le hle)
end Formalism.SLP.P
