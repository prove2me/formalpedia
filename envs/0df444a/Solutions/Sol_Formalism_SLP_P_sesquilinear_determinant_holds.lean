-- Prove2me | solution 1 for Formalism.SLP.P.sesquilinear_determinant_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:43.394771+00:00
-- url     : https://prove2.me/submissions/1cb9e526-22d0-40df-8544-f0a8e7973761

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Hadamard
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
import Theorems.Thm_Formalism_SLP_P_det_orth_sq_le
import Theorems.Thm_Formalism_SLP_P_exists_orth_decomp
import Theorems.Thm_Formalism_SLP_P_norm_det_gram_of_decomp
import Theorems.Thm_Formalism_SLP_P_bmat_eq_of_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset ComplexConjugate
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
namespace Formalism.SLP.P
theorem _root_.solution : Formalism.SLP.SesqDet := by
  intro V₁ V₂ _ _ _ _ B c hB m u w
  have hc : 0 ≤ c ^ (2 * m) := by rw [pow_mul]; positivity
  by_cases hu : LinearIndependent ℂ u
  · by_cases hw : LinearIndependent ℂ w
    · obtain ⟨e, A, he, hA⟩ := exists_orth_decomp u hu
      obtain ⟨f, C, hf, hC⟩ := exists_orth_decomp w hw
      rw [bmat_eq_of_decomp B e f A C u w hA hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
        norm_det_gram_of_decomp e he A u hA, norm_det_gram_of_decomp f hf C w hC, norm_mul, norm_mul, norm_star]
      have h1 := det_orth_sq_le B c hB e he f hf
      calc (‖A.det‖ * ‖(Matrix.of fun k l => B (e k) (f l)).det‖ * ‖C.det‖) ^ 2
          = ‖A.det‖ ^ 2 * ‖(Matrix.of fun k l => B (e k) (f l)).det‖ ^ 2 * ‖C.det‖ ^ 2 := by ring
        _ ≤ ‖A.det‖ ^ 2 * c ^ (2 * m) * ‖C.det‖ ^ 2 := by gcongr
        _ = c ^ (2 * m) * ‖A.det‖ ^ 2 * ‖C.det‖ ^ 2 := by ring
    · obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hw
      have hdet : (Matrix.of fun i j => B (u i) (w j)).det = 0 := by
        refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨fun j => star (g j), fun h0 => hi0 ?_, ?_⟩
        · have := congrFun h0 i0
          simpa using this
        · ext i
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
          have := congrArg (B (u i)) hg
          simp only [map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, map_zero, starRingEnd_apply] at this
          rw [← this]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hdet, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  · obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hu
    have hdet : (Matrix.of fun i j => B (u i) (w j)).det = 0 := by
      refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨g, fun h0 => hi0 (congrFun h0 i0), ?_⟩
      ext j
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      have := congrArg (fun x => B x (w j)) hg
      simp only [map_sum, LinearMap.map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        map_zero, LinearMap.zero_apply] at this
      exact this
    rw [hdet, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
end Formalism.SLP.P
