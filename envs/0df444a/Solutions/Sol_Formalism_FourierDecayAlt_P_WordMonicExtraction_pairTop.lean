-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.pairTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:25.547902+00:00
-- url     : https://prove2.me/submissions/5d3ca1b4-03c4-4d88-a1c4-d6ec7da03a68

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_evR_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_natDegree_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_coeff_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
theorem _root_.solution (Ξ : Sesq M) (P₁ P₂ : R[X]) (a b : ℕ) (h : ℝ) (X X' : M)
    (ha : P₁.natDegree ≤ a) (hb : P₂.natDegree ≤ b) :
    IsTopCoeff (fun Y => Ξ (evR P₁ Y • X) (evR P₂ (Y + h) • X')) (a + b)
      (Ξ (P₁.coeff a • X) (P₂.coeff b • X')) := by
  unfold IsTopCoeff
  refine ⟨∑ i ∈ range (a + 1), ∑ k ∈ range (b + 1),
    Polynomial.C (Ξ (P₁.coeff i • X) (P₂.coeff k • X')) *
      (Polynomial.X ^ i * (Polynomial.X + Polynomial.C (h : ℂ)) ^ k), ?_, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_mono]
    rw [Finset.mem_range] at hi hk
    omega
  · rw [Polynomial.finset_sum_coeff]
    simp_rw [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_range.mpr (Nat.lt_succ_self a)) ?_]
    · rw [Finset.sum_eq_single_of_mem b (Finset.mem_range.mpr (Nat.lt_succ_self b)) ?_]
      · rw [coeff_mono _ _ _ _ _ le_rfl le_rfl, if_pos ⟨rfl, rfl⟩, mul_one]
      · intro k hk hkb
        rw [coeff_mono _ _ _ _ _ le_rfl (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
          if_neg (fun hh => hkb hh.2), mul_zero]
    · intro i hi hia
      apply Finset.sum_eq_zero
      intro k hk
      rw [coeff_mono _ _ _ _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), if_neg (fun hh => hia hh.1), mul_zero]
  · intro Y
    beta_reduce
    rw [evR_smul P₁ a ha Y X, evR_smul P₂ b hb (Y + h) X']
    simp only [map_sum, LinearMap.sum_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, map_pow, map_add, Complex.conj_ofReal,
      Complex.ofReal_add, Finset.mul_sum, Finset.sum_mul]
    first
      | (refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_)); ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_)); ring)
end Formalism.FourierDecayAlt.P.WordMonicExtraction
