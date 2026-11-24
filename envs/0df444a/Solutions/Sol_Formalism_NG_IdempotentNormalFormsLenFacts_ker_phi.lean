-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.ker_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:41.534885+00:00
-- url     : https://prove2.me/submissions/14cdf283-c023-4387-b31d-5ea9ef20776a

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_mk_eq_zero_iff
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_isUnit_det_AK
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_phi_apply
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_map_mulVec_fun

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
theorem _root_.solution (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    LinearMap.ker (phi A) = LinearMap.range (Matrix.mulVecLin A) := by
  have hu := isUnit_det_AK A hd
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range, phi_apply]
  constructor
  · intro h
    choose z hz using fun i => (mk_eq_zero_iff _).mp (congrFun h i)
    refine ⟨z, ?_⟩
    have hz' : (fun j => algebraMap O (FractionRing O) (z j)) =
        (AK A)⁻¹ *ᵥ (fun j => algebraMap O (FractionRing O) (x j)) := funext hz
    funext i
    apply IsFractionRing.injective O (FractionRing O)
    rw [Matrix.mulVecLin_apply]
    have := congrFun (map_mulVec_fun A z) i
    rw [this, hz', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVecLin_apply, map_mulVec_fun, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    ext i
    exact (mk_eq_zero_iff _).mpr ⟨z i, rfl⟩
end Formalism.NG.IdempotentNormalFormsLenFacts
