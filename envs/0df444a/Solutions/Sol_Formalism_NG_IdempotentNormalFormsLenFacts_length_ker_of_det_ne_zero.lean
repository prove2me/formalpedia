-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.length_ker_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:27.173697+00:00
-- url     : https://prove2.me/submissions/766d9687-4566-437c-8ff4-80b170741f5d

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_quot_eq_addVal_det
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_range_phi
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_ker_phi

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι O)
    (hd : A.det ≠ 0) :
    Module.length O (LinearMap.ker (matQ O A)) = addVal O A.det := by
  have hinj : Function.Injective (Matrix.mulVecLin A) :=
    Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
  let N := LinearMap.range (Matrix.mulVecLin A)
  let e : (ι → O) ≃ₗ[O] N := LinearEquiv.ofInjective _ hinj
  have h1 := length_quot_eq_addVal_det N e
  have h2 : N.subtype ∘ₗ (e : (ι → O) →ₗ[O] N) = Matrix.mulVecLin A := LinearMap.ext fun x => rfl
  have h3 : LinearMap.det (Matrix.mulVecLin A) = A.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  rw [← (LinearEquiv.ofEq _ _ (range_phi A hd)).length_eq,
    ← (LinearMap.quotKerEquivRange (phi A)).length_eq,
    (Submodule.quotEquivOfEq _ _ (ker_phi A hd)).length_eq, h1, h2, h3]
end Formalism.NG.IdempotentNormalFormsLenFacts
