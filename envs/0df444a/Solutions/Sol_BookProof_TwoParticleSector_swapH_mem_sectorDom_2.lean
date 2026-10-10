-- Prove2me | solution 2 for BookProof.TwoParticleSector.swapH_mem_sectorDom
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:21:26.633365+00:00
-- url     : https://prove2.me/submissions/dce29141-921b-41c3-b02a-388adb163598

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

theorem solution (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    {x : (Hs.pow 2).carrier} (hx : x ∈ sectorDom Hs D₂ 2) :
    swapH Hs x ∈ sectorDom Hs D₂ 2 := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨swapDom Hs D₂ y, ?_⟩
  have key : (inclPow Hs D₂ 2).toLinearMap ∘ₗ swapDom Hs D₂
      = swapH Hs ∘ₗ (inclPow Hs D₂ 2).toLinearMap := by
    apply TensorProduct.ext'
    intro a w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp only [inclPow, LinearMap.comp_apply]
      erw [swapDom_tmul Hs D₂ a b c]
      simp
      erw [swapH_tmul Hs (a : Hs.carrier) (b : Hs.carrier) c]
    | add u v hu hv =>
      simp only [TensorProduct.tmul_add, map_add] at hu hv ⊢
      rw [hu, hv]
  exact LinearMap.congr_fun key y
