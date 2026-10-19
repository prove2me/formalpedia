-- Prove2me | solution 1 for BookProof.TwoParticleSector.swapTwo_involutive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:29:25.30952+00:00
-- url     : https://prove2.me/submissions/0085decf-c2b5-4e8d-a0ce-e5f03a64ad77

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.swapTwo_involutive
open BookProof.TwoParticleSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
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

theorem solution (t : X ⊗[ℂ] (X ⊗[ℂ] ℂ)) : swapTwo X (swapTwo X t) = t := by
  exact h43_swapTwo_invol t

