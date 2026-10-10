-- Prove2me | solution 2 for BookProof.PermSector.permOp_mem_sectorDom
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:22:32.163881+00:00
-- url     : https://prove2.me/submissions/724eb255-2a63-48dd-9177-79f9a3137462

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.PermSector

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

theorem ps_inclPow_purePow (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) :
    ∀ (n : ℕ) (f : Fin n → (domSpace Hs D₂).carrier),
      inclPow Hs D₂ n (purePow (domSpace Hs D₂) n f)
        = purePow Hs n (fun i => ((f i : D₂) : Hs.carrier)) := by
  intro n
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
    intro f
    rw [purePow_succ, purePow_succ]
    simp only [inclPow]
    erw [TensorProduct.mapIsometry_apply, TensorProduct.map_tmul]
    congr 1
    exact ih (Fin.tail f)

theorem solution (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (n : ℕ) (σ : Equiv.Perm (Fin n))
    {x : (Hs.pow n).carrier}
    (hx : x ∈ sectorDom Hs D₂ n) : permOp Hs n σ x ∈ sectorDom Hs D₂ n := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨permOp (domSpace Hs D₂) n σ y, ?_⟩
  have key : (inclPow Hs D₂ n).toLinearMap ∘ₗ
        (permOp (domSpace Hs D₂) n σ).toLinearEquiv.toLinearMap
      = (permOp Hs n σ).toLinearEquiv.toLinearMap ∘ₗ (inclPow Hs D₂ n).toLinearMap := by
    apply linearMap_ext_purePow
    intro f
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometry.coe_toLinearMap]
    rw [permOp_purePow, ps_inclPow_purePow, ps_inclPow_purePow, permOp_purePow]
    rfl
  exact LinearMap.congr_fun key y
