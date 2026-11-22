-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:40.574814+00:00
-- url     : https://prove2.me/submissions/d8e405e8-b04f-4727-abd7-d3e55363ce54

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
theorem _root_.solution (y : FractionRing O) :
    (Submodule.Quotient.mk y : KO O) = 0 ↔ ∃ x : O, algebraMap O (FractionRing O) x = y := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
end Formalism.NG.IdempotentNormalFormsLenFacts
