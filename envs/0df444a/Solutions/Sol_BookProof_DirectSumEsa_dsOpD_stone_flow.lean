-- Prove2me | solution 1 for BookProof.DirectSumEsa.dsOpD_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:15:30.222704+00:00
-- url     : https://prove2.me/submissions/dd6e37a3-c3aa-4a5d-95e5-d6475efcce44

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.dsOpD_stone_flow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Theorems.Thm_BookProof_DirectSumEsa_subtype_comp_dsOpD
import Theorems.Thm_BookProof_DirectSumEsa_dsCore_dense
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_symmetricOn
import Theorems.Thm_BookProof_DirectSumEsa_essentiallySelfAdjointOn_of_hasZeroDeficiencyOn
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.StoneBridge
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FullEsa
open BookProof BookProof.DirectSumEsa in
theorem solution [∀ i, CompleteSpace (G i)] (A : ∀ i, D i →ₗ[ℂ] D i)
    (hdense : ∀ i, Dense ((D i : Submodule ℂ (G i)) : Set (G i)))
    (hsym : ∀ i, IsSymmetricDom (A i)) (h : ∀ i, HasZeroDeficiencyOn (D i) (A i)) :
    ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint (lp G 2))
      (U : ℝ → (lp G 2 →L[ℂ] lp G 2)),
      EsaClosure.IsSelfAdjointExtension ((dsCore D).subtype.comp (dsOpD A)) T.op ∧
        StoneBridge.IsStoneFlow T U := by 
  have hesa := BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn (fun i => (D i).subtype.comp (A i))
    (fun i => BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn (A i) (h i))
  have hsym' := BookProof.DirectSumEsa.dsOp_symmetricOn (fun i => (D i).subtype.comp (A i))
    (fun i x y => hsym i x y)
  rw [BookProof.DirectSumEsa.subtype_comp_dsOpD]
  exact BookProof.StoneBridge.exists_stone_flow_of_esa _ (BookProof.DirectSumEsa.dsCore_dense hdense) hsym' hesa
