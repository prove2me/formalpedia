-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.sqrtGauss_to_sqrtFock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:45.513346+00:00
-- url     : https://prove2.me/submissions/9b21c99f-fafd-4bb7-930d-e42ea57fe8ff

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_pow_mul_inv_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xFact_mul_xMul
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yFact_mul_yMul
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xMul_ne_zero
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yMul_ne_zero
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xMul_factorization_le
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yMul_factorization_le
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_coeff_cases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
variable {K : Type} [Field K] [CharZero K] {k A B : ℕ} (R : Subring K)
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hR : PLocal R p) {f : PolXY K k}
    (hf : f ∈ PolAB K k A B) (h : f ∈ SqrtGaussLat R (A.factorial * B.factorial)) :
    ((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) • f ∈ SqrtFockLat R := by
  have h' : ∀ m, ((A.factorial * B.factorial : ℕ) : K) * coeff m f ^ 2 ∈ R := h
  show ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m (((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) • f) ^ 2 ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rcases coeff_cases hf m with h0 | ⟨hx, hy⟩
  · rw [h0]
    simp
  · have hxb : (xMul m).factorization p ≤ (k - 1) * Nat.log p (A + B + k) :=
      le_trans (xMul_factorization_le p m) (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega)))
    have hyb : (yMul m).factorization p ≤ (k - 1) * Nat.log p (A + B + k) :=
      le_trans (yMul_factorization_le p m) (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega)))
    have hx1 := pow_mul_inv_mem R hp hR (xMul_ne_zero m) hxb
    have hy1 := pow_mul_inv_mem R hp hR (yMul_ne_zero m) hyb
    have hxf : (xMul m : K) ≠ 0 := by exact_mod_cast xMul_ne_zero m
    have hyf : (yMul m : K) ≠ 0 := by exact_mod_cast yMul_ne_zero m
    have hm := h' m
    rw [← hx, ← hy, ← xFact_mul_xMul, ← yFact_mul_yMul] at hm
    push_cast at hm
    have e : ((xFact m : K) * (yFact m : K)) * (((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) * coeff m f) ^ 2 =
        ((((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) * (xMul m : K)⁻¹) * (((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) * (yMul m : K)⁻¹)) *
        ((xFact m : K) * (xMul m : K) * ((yFact m : K) * (yMul m : K)) * coeff m f ^ 2) := by
      first | (field_simp; ring) | field_simp
    rw [e]
    first | exact R.mul_mem (R.mul_mem hx1 hy1) hm |
      (convert R.mul_mem (R.mul_mem hx1 hy1) hm using 2; ring)
end Formalism.CountingSumsFrames.Har4
