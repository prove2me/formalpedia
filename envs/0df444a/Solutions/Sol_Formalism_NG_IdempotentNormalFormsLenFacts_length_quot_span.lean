-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:42.7029+00:00
-- url     : https://prove2.me/submissions/93a0ce2f-f530-4f89-b8f2-00790beadf12

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentNormalFormsLenFacts
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.NG.IdempotentNormalFormsLenFacts
theorem _root_.solution (a : O) :
    Module.length O (O ⧸ Ideal.span ({a} : Set O)) = addVal O a :=
  Ring.ord_eq_addVal a
end Formalism.NG.IdempotentNormalFormsLenFacts
