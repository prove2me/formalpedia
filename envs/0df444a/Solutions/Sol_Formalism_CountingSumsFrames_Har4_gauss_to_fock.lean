-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.gauss_to_fock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:44.629045+00:00
-- url     : https://prove2.me/submissions/bec128af-781b-4bce-844b-604bff3fb1e1

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_pow_mul_inv_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xFact_mul_xMul
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xMul_ne_zero
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xMul_factorization_le
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xFact_ne_zero
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
    (h : f ∈ GaussLat R) :
    ((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f ∈ FockLat R := by
  have h' : ∀ m, coeff m f ∈ R := h
  show ∀ m, (xFact m : K) * coeff m (((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rcases coeff_cases hf m with h0 | ⟨hx, -⟩
  · rw [h0, mul_zero, mul_zero]
    exact R.zero_mem
  · have hxm := xMul_ne_zero m
    have hxf : (xFact m : K) ≠ 0 := by exact_mod_cast xFact_ne_zero m
    have hmem := pow_mul_inv_mem R hp hR hxm (xMul_factorization_le p m)
    rw [← hx, ← xFact_mul_xMul, Nat.cast_mul, mul_inv]
    have e : (xFact m : K) * ((p : K) ^ ((k - 1) * Nat.log p (xDeg m)) *
        ((xFact m : K)⁻¹ * (xMul m : K)⁻¹) * coeff m f) =
        ((p : K) ^ ((k - 1) * Nat.log p (xDeg m)) * (xMul m : K)⁻¹) * coeff m f := by
      field_simp
    rw [e]
    exact R.mul_mem hmem (h' m)
end Formalism.CountingSumsFrames.Har4
