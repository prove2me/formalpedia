-- Prove2me | solution 2 for BookProof.TwoParticleSector.swapH_involutive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:16:08.399697+00:00
-- url     : https://prove2.me/submissions/c16ca778-653f-45d0-bea9-5a91f3d8b11a

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.swapH_involutive
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorCore
open BookProof.TwoParticleSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
open BookProof.TwoParticleSector

theorem solution(t : (Hs.pow 2).carrier) : swapH Hs (swapH Hs t) = t := by
  revert t
  show ∀ t : TensorProduct ℂ Hs.carrier (TensorProduct ℂ Hs.carrier ℂ), swapH Hs (swapH Hs t) = t
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x yz =>
    induction yz using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul y c => exact (congrArg (swapH Hs) (swapH_tmul (x := x) (y := y) (c := c))).trans (swapH_tmul (x := y) (y := x) (c := c))
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]
