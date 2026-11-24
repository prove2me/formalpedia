-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.IsUB.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:25:01.771334+00:00
-- url     : https://prove2.me/submissions/c3fdb32c-58c6-408d-8510-8cfdf0acfc8d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_IsUB_zero_of_lt
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_IsUB_zero_of_blk
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_IsUB_det_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {m : ℕ}
namespace Formalism.L2.S.L6.UnitaryStandardVectors
namespace IsUB
theorem _root_.solution {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) : IsUB blk C⁻¹ := by
  have hup : C.BlockTriangular id := by
    intro i j hij
    exact h.zero_of_lt hij
  have hb1 : C.BlockTriangular blk := by
    intro i j hij
    exact h.zero_of_blk hij.ne'
  have hb2 : C.BlockTriangular (fun i => OrderDual.toDual (blk i)) := by
    intro i j hij
    exact h.zero_of_blk (OrderDual.toDual_lt_toDual.mp hij).ne
  have hdet : IsUnit C.det := by
    rw [h.det_eq_one]
    exact isUnit_one
  letI : Invertible C := C.invertibleOfIsUnitDet hdet
  have iup := Matrix.blockTriangular_inv_of_blockTriangular hup
  have ib1 := Matrix.blockTriangular_inv_of_blockTriangular hb1
  have ib2 := Matrix.blockTriangular_inv_of_blockTriangular hb2
  refine ⟨fun i => ?_, fun i j hij => ⟨?_, ?_⟩⟩
  · have h1 : (C * C⁻¹) i i = 1 := by
      rw [Matrix.mul_nonsing_inv _ hdet, one_apply_eq]
    rw [mul_apply, Finset.sum_eq_single i] at h1
    · rwa [h.1, one_mul] at h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [h.zero_of_lt hlt, zero_mul]
      · rw [iup hlt, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · by_contra hlt
    exact hij (iup (not_le.mp hlt))
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hij (ib2 (OrderDual.toDual_lt_toDual.mpr hlt))
    · exact hij (ib1 hlt)
end IsUB
end Formalism.L2.S.L6.UnitaryStandardVectors
