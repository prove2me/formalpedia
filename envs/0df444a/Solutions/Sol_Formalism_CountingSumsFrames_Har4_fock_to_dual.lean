-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.fock_to_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:34.364075+00:00
-- url     : https://prove2.me/submissions/573766fe-0ae7-4324-962d-df3b01ccba33

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_pow_mul_inv_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yFact_mul_yMul
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yMul_ne_zero
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yMul_factorization_le
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yFact_ne_zero
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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hR : PLocal R p) {f : PolXY K k} (hf : f ∈ PolAB K k A B)
    (h : f ∈ FockLat R) :
    ((p : K) ^ ((k - 1) * Nat.log p B) * (B.factorial : K)⁻¹) • f ∈ DualLat R := by
  have h' : ∀ m, (xFact m : K) * coeff m f ∈ R := h
  show ∀ m, ((xFact m : K) * (yFact m : K)) *
    coeff m (((p : K) ^ ((k - 1) * Nat.log p B) * (B.factorial : K)⁻¹) • f) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rcases coeff_cases hf m with h0 | ⟨-, hy⟩
  · rw [h0, mul_zero, mul_zero]
    exact R.zero_mem
  · have hym := yMul_ne_zero m
    have hyf : (yFact m : K) ≠ 0 := by exact_mod_cast yFact_ne_zero m
    have hmem := pow_mul_inv_mem R hp hR hym (yMul_factorization_le p m)
    rw [← hy, ← yFact_mul_yMul, Nat.cast_mul, mul_inv]
    have e : ((xFact m : K) * (yFact m : K)) * ((p : K) ^ ((k - 1) * Nat.log p (yDeg m)) *
        ((yFact m : K)⁻¹ * (yMul m : K)⁻¹) * coeff m f) =
        ((p : K) ^ ((k - 1) * Nat.log p (yDeg m)) * (yMul m : K)⁻¹) * ((xFact m : K) * coeff m f) := by
      field_simp
    rw [e]
    exact R.mul_mem hmem (h' m)
end Formalism.CountingSumsFrames.Har4
