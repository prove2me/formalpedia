-- Prove2me | solution 1 for BookProof.DirectSumEsa.fockH_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:18:00.364898+00:00
-- url     : https://prove2.me/submissions/72613004-3323-42c2-963c-9c3a61e859e2

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.fockH_stone_flow
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Theorems.Thm_BookProof_DirectSumEsa_subtype_comp_dsOpD
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_symmetricOn
import Theorems.Thm_BookProof_DirectSumEsa_essentiallySelfAdjointOn_of_hasZeroDeficiencyOn
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_multOp_isSymmetricDom
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_multOp_hasZeroDeficiencyOn
import Theorems.Thm_BookProof_DirectSumEsa_fockCore_dense
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.StoneBridge
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
open BookProof BookProof.DirectSumEsa in
theorem ds_gen_esa (A : ∀ i, D i →ₗ[ℂ] D i) (h : ∀ i, BookProof.NavierStokesFlow.HasZeroDeficiencyOn (D i) (A i)) :
    EssentiallySelfAdjointOn (dsCore D) ((dsCore D).subtype.comp (dsOpD A)) := by
  rw [BookProof.DirectSumEsa.subtype_comp_dsOpD]
  exact BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn _ (fun i =>
    BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn (A i) (h i))

open BookProof BookProof.DirectSumEsa in
theorem ds_gen_sym (A : ∀ i, D i →ₗ[ℂ] D i) (hsym : ∀ i, BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom (A i)) :
    SymmetricOn (dsCore D) ((dsCore D).subtype.comp (dsOpD A)) := by
  rw [BookProof.DirectSumEsa.subtype_comp_dsOpD]
  exact BookProof.DirectSumEsa.dsOp_symmetricOn _ (fun i x y => hsym i x y)

open BookProof BookProof.DirectSumEsa in
theorem solution {w : ℝ → ℝ} (hw : Measurable w) :
    ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint fockSpace)
      (U : ℝ → (fockSpace →L[ℂ] fockSpace)),
      EsaClosure.IsSelfAdjointExtension ((fockCore w).subtype.comp (fockH hw)) T.op ∧
        StoneBridge.IsStoneFlow T U := by 
  have hesa : EssentiallySelfAdjointOn (fockCore w) ((fockCore w).subtype.comp (fockH hw)) :=
    ds_gen_esa _ (fun n => by exact BookProof.NavierStokesFlow.FockContinuum.multOp_hasZeroDeficiencyOn _ _)
  have hsym : SymmetricOn (fockCore w) ((fockCore w).subtype.comp (fockH hw)) :=
    ds_gen_sym _ (fun n => by exact BookProof.NavierStokesFlow.FockContinuum.multOp_isSymmetricDom _ _)
  exact BookProof.StoneBridge.exists_stone_flow_of_esa _ (BookProof.DirectSumEsa.fockCore_dense hw) hsym hesa
