-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.map_mulVec_fun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:50.834118+00:00
-- url     : https://prove2.me/submissions/02a94b0b-2014-45c0-ab66-09d3bf663a23

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
theorem _root_.solution (A : Matrix ι ι O) (z : ι → O) :
    (fun i => algebraMap O (FractionRing O) ((A *ᵥ z) i)) =
      AK A *ᵥ (fun j => algebraMap O (FractionRing O) (z j)) := by
  ext i
  exact RingHom.map_mulVec _ A z i
end Formalism.NG.IdempotentNormalFormsLenFacts
