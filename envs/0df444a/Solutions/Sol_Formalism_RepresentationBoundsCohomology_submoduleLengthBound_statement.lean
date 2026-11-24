-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:07.101068+00:00
-- url     : https://prove2.me/submissions/65f42b20-8e04-4808-8c92-f8ca6244c325

import Definitions.Def_Formalism_WachLatticeTwists_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_SubmoduleLengthBoundStatement
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_quot_span
import Theorems.Thm_Formalism_NG_lenKer


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
open Formalism Formalism.RepresentationBoundsCohomology
namespace Formalism.RepresentationBoundsCohomology
theorem _root_.solution : Formalism.RepresentationBoundsCohomology.SubmoduleLengthBound := by
  intro O _ _ _ d _ N ℓ c hN
  classical

  let e : d ≃ Fin (Fintype.card d) := Fintype.equivFin d
  let A : Matrix (Fin (Fintype.card d)) (Fin (Fintype.card d)) O :=
    Matrix.diagonal (fun _ => (ℓ : O) ^ c)
  have hA : ∀ v : Fin (Fintype.card d) → Formalism.NG.KO O,
      Formalism.NG.matQ O A v = ((ℓ : O) ^ c) • v := by
    intro v
    funext i
    simp [Formalism.NG.matQ, Formalism.NG.relMap, A, Matrix.diagonal_apply, ite_smul]
  let g : (d → Formalism.NG.KO O) →ₗ[O] (Fin (Fintype.card d) → Formalism.NG.KO O) :=
    LinearMap.funLeft O (Formalism.NG.KO O) e.symm
  have hg : Function.Injective g :=
    LinearMap.funLeft_injective_of_surjective _ _ _ e.symm.surjective
  let f : N →ₗ[O] LinearMap.ker (Formalism.NG.matQ O A) :=
    LinearMap.codRestrict _ (g.comp N.subtype) (by
      intro x
      rw [LinearMap.mem_ker, hA]
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [← map_smul, hN x x.2, map_zero])
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply hg
    have := congrArg Subtype.val hxy
    simpa [f] using this
  have h1 := Module.length_le_of_injective f hf
  rw [Formalism.NG.lenKer O (Fin (Fintype.card d)) A] at h1
  have hdet : A.det = ((ℓ : O) ^ c) ^ Fintype.card d := by
    simp [A, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
  rw [hdet, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_pow] at h1
  rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]
  simpa [nsmul_eq_mul] using h1
end Formalism.RepresentationBoundsCohomology
