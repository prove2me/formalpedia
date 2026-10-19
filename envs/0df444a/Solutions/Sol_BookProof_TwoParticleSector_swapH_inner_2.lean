-- Prove2me | solution 2 for BookProof.TwoParticleSector.swapH_inner
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:29:54.016942+00:00
-- url     : https://prove2.me/submissions/f5c1822a-b489-4cfc-837d-ffa8c50bca87

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterTensorGraphCore
-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.swapH_inner
open BookProof.TensorCore
open BookProof.TwoParticleSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
theorem h43_swapTwo_inner {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (t s : Y ⊗[ℂ] (Y ⊗[ℂ] ℂ)) :
    (inner ℂ (swapTwo Y t) (swapTwo Y s) : ℂ) = inner ℂ t s := by
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (swapTwo Y t), inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) t s]
  have h1 : ∀ c : ℂ, swapTwo Y t + c • swapTwo Y s = swapTwo Y (t + c • s) := fun c => by
    rw [LinearIsometryEquiv.map_add, LinearIsometryEquiv.map_smul]
  have h2 : ∀ c : ℂ, swapTwo Y t - c • swapTwo Y s = swapTwo Y (t - c • s) := fun c => by
    rw [LinearIsometryEquiv.map_sub, LinearIsometryEquiv.map_smul]
  have h3 : swapTwo Y t + swapTwo Y s = swapTwo Y (t + s) := by rw [LinearIsometryEquiv.map_add]
  have h4 : swapTwo Y t - swapTwo Y s = swapTwo Y (t - s) := by rw [LinearIsometryEquiv.map_sub]
  rw [h3, h4, h1, h2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

theorem h43_swapTwo_invol {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (t : Y ⊗[ℂ] (Y ⊗[ℂ] ℂ)) : swapTwo Y (swapTwo Y t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [LinearIsometryEquiv.map_zero, LinearIsometryEquiv.map_zero]
  | tmul x yc =>
    induction yc using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, LinearIsometryEquiv.map_zero, LinearIsometryEquiv.map_zero]
    | tmul y c => rw [swapTwo_tmul, swapTwo_tmul]
    | add a b ha hb => rw [TensorProduct.tmul_add, LinearIsometryEquiv.map_add, LinearIsometryEquiv.map_add, ha, hb]
  | add a b ha hb => rw [LinearIsometryEquiv.map_add, LinearIsometryEquiv.map_add, ha, hb]

theorem solution (t s : (Hs.pow 2).carrier) :
    (inner ℂ (swapH Hs t) (swapH Hs s) : ℂ) = inner ℂ t s := by
  exact h43_swapTwo_inner (Y := Hs.carrier) t s

