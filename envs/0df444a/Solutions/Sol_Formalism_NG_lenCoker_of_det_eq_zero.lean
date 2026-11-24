-- Prove2me | solution 1 for Formalism.NG.lenCoker_of_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:41.790321+00:00
-- url     : https://prove2.me/submissions/bf0f05bd-39ee-42a5-a935-8d3f4befb642

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_quot_span


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
theorem _root_.solution (A : Matrix ι ι O) (hd : A.det = 0) :
    Module.length O ((ι → O) ⧸ LinearMap.range (Matrix.mulVecLin A)) = ⊤ := by
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fun i => addVal O (w i))
    ⟨j, Finset.mem_univ _⟩
  have hwi0 : w i0 ≠ 0 := by
    intro h
    have := hi0 j (Finset.mem_univ _)
    rw [h, addVal_zero, top_le_iff, addVal_eq_top_iff] at this
    exact hj this
  choose w' hw' using fun i => (addVal_le_iff_dvd (a := w i0) (b := w i)).mp
    (hi0 i (Finset.mem_univ _))
  have hw'i0 : w' i0 = 1 := by
    have := hw' i0
    exact (mul_left_cancel₀ hwi0 (this.symm.trans (mul_one _).symm))
  have hw'A : w' ᵥ* A = 0 := by
    have : w = w i0 • w' := funext fun i => by simp [hw' i]
    rw [this, Matrix.smul_vecMul] at hw
    exact (smul_eq_zero.mp hw).resolve_left hwi0
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  rw [ENat.eq_top_iff_forall_ge]
  intro k
  let I : Ideal O := Ideal.span ({ϖ ^ k} : Set O)
  let f : (ι → O) →ₗ[O] (O ⧸ I) := I.mkQ ∘ₗ dotLin w'
  have hle : LinearMap.range (Matrix.mulVecLin A) ≤ LinearMap.ker f := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    show I.mkQ (w' ⬝ᵥ (A *ᵥ z)) = 0
    rw [Matrix.dotProduct_mulVec, hw'A, zero_dotProduct, map_zero]
  let F := (LinearMap.range (Matrix.mulVecLin A)).liftQ f hle
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨c, rfl⟩ := I.mkQ_surjective y
    refine ⟨Submodule.Quotient.mk (Pi.single i0 c), ?_⟩
    show I.mkQ (w' ⬝ᵥ Pi.single i0 c) = I.mkQ c
    rw [dotProduct_single, hw'i0, one_mul]
  have h := Module.length_le_of_surjective F hF
  rw [IdempotentNormalFormsLenFacts.length_quot_span, hϖ.addVal_pow] at h
  simpa using h
end Formalism.NG
