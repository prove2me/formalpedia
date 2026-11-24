-- Prove2me | solution 1 for Formalism.L2.Pj.upper_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:16:43.860728+00:00
-- url     : https://prove2.me/submissions/ff218da9-61a6-42a3-a74f-8dec06f6a71d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open Matrix IsDedekindDomain
variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]
namespace Formalism.L2.Pj
theorem _root_.solution {m : ℕ} (U : Matrix (Fin m) (Fin m) F) (hU : U.BlockTriangular id) (hd : ∀ i, U i i ≠ 0) :
    U⁻¹.BlockTriangular id ∧ (∀ i, U⁻¹ i i ≠ 0) ∧ U * U⁻¹ = 1 := by
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hU]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  letI := Matrix.invertibleOfIsUnitDet U hu
  have hinv : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hU
  refine ⟨hinv, fun i => ?_, Matrix.mul_nonsing_inv U hu⟩
  have h1 : (U⁻¹ * U) i i = 1 := by rw [Matrix.nonsing_inv_mul U hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hinv hlt, zero_mul]
    · rw [hU hgt, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
end Formalism.L2.Pj
