-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.pairing_top_degree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:37.862275+00:00
-- url     : https://prove2.me/submissions/8fa61b98-7e38-4fe6-bcdf-3445d055a9d4

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_evR_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_natDegree_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_coeff_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.TopDegreePolynomials
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.PairTop := by
  intro R M _ _ _ _ _ _ Ξ P₁ P₂ a b h X X' ha hb
  refine ⟨∑ i ∈ range (a + 1), ∑ j ∈ range (b + 1),
    C (Ξ (P₁.coeff i • X) (P₂.coeff j • X')) * ((Polynomial.X : ℂ[X]) ^ i *
      (Polynomial.X + C (h : ℂ)) ^ j), ?_, ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_mono]
    have := Finset.mem_range.mp hi
    have := Finset.mem_range.mp hj
    omega
  · rw [finsetSum_coeff]
    rw [Finset.sum_eq_single a]
    · rw [finsetSum_coeff, Finset.sum_eq_single b]
      · rw [coeff_C_mul, coeff_mono _ _ _ _ _ le_rfl le_rfl]; simp
      · intro j hj hjb
        rw [coeff_C_mul, coeff_mono _ _ _ _ _ le_rfl (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
        simp [hjb]
      · intro hb'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self b)) hb'
    · intro i hi hia
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [coeff_C_mul, coeff_mono _ _ _ _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
      simp [hia]
    · intro ha'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self a)) ha'
  · intro Y
    simp only []
    rw [evR_smul P₁ a ha, evR_smul P₂ b hb, map_sum Ξ, LinearMap.sum_apply, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul Ξ, LinearMap.smul_apply, map_smulₛₗ]
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, smul_eq_mul, map_pow,
      map_add, Complex.conj_ofReal, Complex.ofReal_add]
    ring
end Formalism.FourierDecayAlt.P
