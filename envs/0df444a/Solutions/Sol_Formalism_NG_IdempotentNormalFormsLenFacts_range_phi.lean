-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.range_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:43.231021+00:00
-- url     : https://prove2.me/submissions/4bab5995-af19-4cc3-bfd0-9aa9e6e0cb19

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_mk_eq_zero_iff
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_matQ_mk
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_isUnit_det_AK
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_phi_apply

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
    LinearMap.range (phi A) = LinearMap.ker (matQ O A) := by
  have hu := isUnit_det_AK A hd
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, phi_apply, matQ_mk, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    ext i
    exact (mk_eq_zero_iff _).mpr ⟨x i, rfl⟩
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    choose y hy using fun i => Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (v i)
    have hv' : v = fun i => (Submodule.Quotient.mk (y i) : KO O) := funext fun i => (hy i).symm
    rw [hv', matQ_mk] at hv
    choose x hx using fun i => (mk_eq_zero_iff _).mp (congrFun hv i)
    refine ⟨x, ?_⟩
    have hx' : (fun j => algebraMap O (FractionRing O) (x j)) = AK A *ᵥ y := funext hx
    rw [phi_apply, hx', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, hv']
end Formalism.NG.IdempotentNormalFormsLenFacts
