-- Prove2me | solution 1 for DeletionCode.SupportInclusion.supportComponentMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:09:04.42496+00:00
-- url     : https://prove2.me/submissions/9ca792aa-3916-4e94-aa01-0b79223a54ce

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SupportInclusion

set_option autoImplicit true
open DeletionCode DeletionCode.SupportInclusion
open SignedSupport SupportComponents RuleSetGraph
namespace DeletionCode.SupportInclusion
theorem _root_.solution {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) (v : RuleSetVertex Q) :
    supportComponentMap hsub (Quotient.mk (ruleSetSetoid Q) v) =
      Quotient.mk (ruleSetSetoid S) ⟨v.val, incident_mono hsub v.property⟩ := rfl
end DeletionCode.SupportInclusion
