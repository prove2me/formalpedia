-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.sqrtFock_to_sqrtGauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:45.43286+00:00
-- url     : https://prove2.me/submissions/7c090f5a-26d3-4777-8811-65083ac063a1

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xFact_mul_xMul
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yFact_mul_yMul
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
theorem _root_.solution {f : PolXY K k} (hf : f ∈ PolAB K k A B) (h : f ∈ SqrtFockLat R) :
    f ∈ SqrtGaussLat R (A.factorial * B.factorial) := by
  have h' : ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m f ^ 2 ∈ R := h
  show ∀ m, ((A.factorial * B.factorial : ℕ) : K) * coeff m f ^ 2 ∈ R
  intro m
  rcases coeff_cases hf m with h0 | ⟨hx, hy⟩
  · rw [h0]
    simp
  · rw [← hx, ← hy, ← xFact_mul_xMul, ← yFact_mul_yMul]
    push_cast
    have e : (xFact m : K) * (xMul m : K) * ((yFact m : K) * (yMul m : K)) * coeff m f ^ 2 =
        ((xMul m : K) * (yMul m : K)) * (((xFact m : K) * (yFact m : K)) * coeff m f ^ 2) := by ring
    rw [e]
    exact R.mul_mem (R.mul_mem (natCast_mem R _) (natCast_mem R _)) (h' m)
end Formalism.CountingSumsFrames.Har4
