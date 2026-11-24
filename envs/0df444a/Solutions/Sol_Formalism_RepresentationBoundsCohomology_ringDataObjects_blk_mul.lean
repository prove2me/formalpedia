-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.blk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:36.992198+00:00
-- url     : https://prove2.me/submissions/9bf3cb8e-c13f-4fd2-b56c-c22be79ebc51

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_BurnsideMat
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RankDiagIte

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
variable {A : Type*} [CommRing A] {d : Type} [Fintype d] [DecidableEq d] {α : Type} [DecidableEq α]
  (bl : d → α)
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {M N : Matrix d d A} (hM : ∀ i j, bl i ≠ bl j → M i j = 0) (c : α) :
    (M * N).toSquareBlock bl c = M.toSquareBlock bl c * N.toSquareBlock bl c := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.mul_apply]
  have h0 : ∑ k : {k // ¬ bl k = c}, M i (k : d) * N (k : d) j = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hM i k (by rw [hi]; exact Ne.symm k.2), zero_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => bl k = c) (fun k => M i k * N k j), h0,
    add_zero]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
