-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.fock_to_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:11.99074+00:00
-- url     : https://prove2.me/submissions/d0a3c739-5b65-4bb7-bf9f-fe4cefb67252

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xFact_mul_xMul
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
theorem _root_.solution {f : PolXY K k} (hf : f ∈ PolAB K k A B) (h : f ∈ FockLat R) :
    (A.factorial : K) • f ∈ GaussLat R := by
  have h' : ∀ m, (xFact m : K) * coeff m f ∈ R := h
  show ∀ m, coeff m ((A.factorial : K) • f) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rcases coeff_cases hf m with h0 | ⟨hx, -⟩
  · rw [h0, mul_zero]
    exact R.zero_mem
  · rw [← hx, ← xFact_mul_xMul, Nat.cast_mul, mul_comm (xFact m : K), mul_assoc]
    exact R.mul_mem (natCast_mem R _) (h' m)
end Formalism.CountingSumsFrames.Har4
