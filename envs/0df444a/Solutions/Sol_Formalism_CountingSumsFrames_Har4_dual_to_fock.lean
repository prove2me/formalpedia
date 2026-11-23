-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.dual_to_fock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:40:55.968143+00:00
-- url     : https://prove2.me/submissions/92be4ed2-654f-466c-ba93-638d480b9141

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
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
theorem _root_.solution {f : PolXY K k} (hf : f ∈ PolAB K k A B) (h : f ∈ DualLat R) :
    (B.factorial : K) • f ∈ FockLat R := by
  have h' : ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m f ∈ R := h
  show ∀ m, (xFact m : K) * coeff m ((B.factorial : K) • f) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rcases coeff_cases hf m with h0 | ⟨-, hy⟩
  · rw [h0, mul_zero, mul_zero]
    exact R.zero_mem
  · rw [← hy, ← yFact_mul_yMul, Nat.cast_mul]
    have e : (xFact m : K) * (((yFact m : K) * (yMul m : K)) * coeff m f) =
        (yMul m : K) * (((xFact m : K) * (yFact m : K)) * coeff m f) := by ring
    rw [e]
    exact R.mul_mem (natCast_mem R _) (h' m)
end Formalism.CountingSumsFrames.Har4
