-- Prove2me | solution 1 for Formalism.L2.DIV.sig0Conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:55.609142+00:00
-- url     : https://prove2.me/submissions/ebe323d4-bc8b-4066-bf35-584a3bed0947

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
import Theorems.Thm_Formalism_L2_DIV_CoF_val_star


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : DistinguishedEmbeddingConjugation := by
  intro ι LL _ x
  show ι (CoF.val ι LL (star x)) = _
  rw [CoF.val_star, conjQb_spec]
  rfl
end Formalism.L2.DIV
