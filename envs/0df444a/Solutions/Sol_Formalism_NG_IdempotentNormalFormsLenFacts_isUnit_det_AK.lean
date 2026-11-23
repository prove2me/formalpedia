-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.isUnit_det_AK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:50.280796+00:00
-- url     : https://prove2.me/submissions/979b7bfe-c321-4b6e-b24b-7888f317e8ca

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
theorem _root_.solution (A : Matrix ι ι O) (hd : A.det ≠ 0) : IsUnit (AK A).det := by
  rw [isUnit_iff_ne_zero, AK, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact fun h => hd (IsFractionRing.injective O (FractionRing O) (by rw [h, map_zero]))
end Formalism.NG.IdempotentNormalFormsLenFacts
