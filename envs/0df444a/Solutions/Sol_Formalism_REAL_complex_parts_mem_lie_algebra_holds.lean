-- Prove2me | solution 1 for Formalism.REAL.complex_parts_mem_lie_algebra_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:34.849911+00:00
-- url     : https://prove2.me/submissions/a1f625f5-3bc8-4195-9be3-7714dcd9fdf7

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Theorems.Thm_Formalism_REAL_signature_mul_signature_mul
import Theorems.Thm_Formalism_REAL_cartan_involution_conjTranspose_mul
import Theorems.Thm_Formalism_REAL_signature_mul_cartan_involution
import Theorems.Thm_Formalism_REAL_star_one_half
import Theorems.Thm_Formalism_REAL_star_one_div_two_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution : CpartMem := by
  intro n ε Z
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold inG cpart1
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul,
      cartan_involution_conjTranspose_mul, Matrix.mul_smul, Matrix.mul_sub, signature_mul_cartan_involution, star_one_half, ← smul_add]
    simp
  · unfold inG cpart2
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul,
      cartan_involution_conjTranspose_mul, Matrix.mul_smul, Matrix.mul_add, signature_mul_cartan_involution, star_one_div_two_I, neg_smul,
      add_comm (Jm ε * Z), neg_add_cancel]
  · unfold cpart1 cpart2
    rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
    norm_num
  · intro hX
    unfold inG at hX
    have hA : Jm ε * Zᴴ * Jm ε = -Z := by
      rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hX, Matrix.mul_neg, signature_mul_signature_mul]
    unfold cpart1 cpart2
    rw [hA, sub_neg_eq_add, add_neg_cancel, smul_zero, ← two_smul ℂ Z, smul_smul]
    norm_num
end Formalism.REAL
