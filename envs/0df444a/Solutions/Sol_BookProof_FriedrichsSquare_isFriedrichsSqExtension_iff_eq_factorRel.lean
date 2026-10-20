-- Prove2me | solution 1 for BookProof.FriedrichsSquare.isFriedrichsSqExtension_iff_eq_factorRel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:38:43.395342+00:00
-- url     : https://prove2.me/submissions/6c765d6b-eac2-40bf-affd-5aae83bd8543

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.isFriedrichsSqExtension_iff_eq_factorRel
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Theorems.Thm_BookProof_FriedrichsSquare_le_factorRel_of_symmetric_extension
import Theorems.Thm_BookProof_FriedrichsSquare_IsFriedrichsSqExtension_symmetric
import Theorems.Thm_BookProof_FriedrichsSquare_adjPairs_mono
import Theorems.Thm_BookProof_FriedrichsSquare_adjPairs_factorRel
import Theorems.Thm_BookProof_FriedrichsSquare_fst_mem_clDom_of_mem_factorRel
import Theorems.Thm_BookProof_ClosureUniqueness_mem_factorGraph_sqOp
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStoneConverse
open BookProof.ClosureUniqueness
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]
open BookProof.FriedrichsSquare in
theorem solution [CompleteSpace F] {A : D →ₗ[ℂ] F}
    (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {R : Submodule ℂ (F × F)} :
    IsFriedrichsSqExtension A hstab R ↔ R = factorRel A := by
  constructor
  · intro h
    have hle : R ≤ factorRel A :=
      le_factorRel_of_symmetric_extension hsym h.extends_sq h.symmetric h.form_domain
    refine le_antisymm hle ?_
    have := adjPairs_mono hle
    rw [adjPairs_factorRel, h.selfAdjoint] at this
    exact this
  · rintro rfl
    exact ⟨fun v => mem_factorGraph_sqOp A hsym hstab v,
      fun p hp => fst_mem_clDom_of_mem_factorRel hp, adjPairs_factorRel A⟩
