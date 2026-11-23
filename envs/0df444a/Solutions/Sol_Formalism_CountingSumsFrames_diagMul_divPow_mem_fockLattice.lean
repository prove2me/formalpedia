-- Prove2me | solution 1 for Formalism.CountingSumsFrames.diagMul_divPow_mem_fockLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:09.812522+00:00
-- url     : https://prove2.me/submissions/444c810a-42cb-405c-a6b6-1c629b0f4830

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_xFactorial_add_diagExponent
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_diagMul_pow
import Theorems.Thm_Formalism_CountingSumsFrames_descFactorial_cast_eq

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
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (R : Subring K) (i : Fin k) (n : ℕ) (f : PolXY K k) (hf : f ∈ FockLat R) :
    (((n.factorial : K)⁻¹) • h3e K i ^ n) f ∈ FockLat R := by
  intro m
  rw [LinearMap.smul_apply, coeff_smul, smul_eq_mul, coeff_diagMul_pow]
  split_ifs with h
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + h3s i n := ⟨m - h3s i n, (tsub_add_cancel_of_le h).symm⟩
    rw [add_tsub_cancel_right, xFactorial_add_diagExponent]
    have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have : (((m' (Sum.inl i) + n).descFactorial n * xFact m' : ℕ) : K) * ((n.factorial : K)⁻¹ * coeff m' f) =
        (((m' (Sum.inl i) + n).choose n : ℕ) : K) * ((xFact m' : K) * coeff m' f) := by
      rw [Nat.cast_mul, descFactorial_cast_eq]
      field_simp
    rw [this]
    exact R.mul_mem (natCast_mem R _) (hf m')
  · simp
end Formalism.CountingSumsFrames
