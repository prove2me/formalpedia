-- Prove2me | solution 1 for Formalism.NG.lenCoker_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:42.603297+00:00
-- url     : https://prove2.me/submissions/4a9d913f-39be-4f3b-836c-b08fa7222a44

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_quot_eq_addVal_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.NG
theorem _root_.solution (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    Module.length O ((ι → O) ⧸ LinearMap.range (Matrix.mulVecLin A)) = addVal O A.det := by
  have hinj : Function.Injective (Matrix.mulVecLin A) :=
    Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
  let N := LinearMap.range (Matrix.mulVecLin A)
  let e : (ι → O) ≃ₗ[O] N := LinearEquiv.ofInjective _ hinj
  have h1 := IdempotentNormalFormsLenFacts.length_quot_eq_addVal_det N e
  have h2 : N.subtype ∘ₗ (e : (ι → O) →ₗ[O] N) = Matrix.mulVecLin A := LinearMap.ext fun x => rfl
  have h3 : LinearMap.det (Matrix.mulVecLin A) = A.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  rw [h1, h2, h3]
end Formalism.NG
