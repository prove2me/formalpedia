-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.phi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:51.131651+00:00
-- url     : https://prove2.me/submissions/c3600e04-7478-4d40-952f-20067939055f

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.NG.IdempotentNormalFormsLenFacts
theorem _root_.solution (A : Matrix ι ι O) (x : ι → O) :
    phi A x = fun i => (Submodule.Quotient.mk
      (((AK A)⁻¹ *ᵥ (fun j => algebraMap O (FractionRing O) (x j))) i) : KO O) := rfl
end Formalism.NG.IdempotentNormalFormsLenFacts
