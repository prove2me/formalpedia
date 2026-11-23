-- Prove2me | solution 1 for Formalism.CountingSumsFrames.diagLaplacian_divPow_mem_fockLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:09.156203+00:00
-- url     : https://prove2.me/submissions/64c45c12-2240-461a-ae94-74483767f6d9

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_xFactorial_add_diagExponent
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_diagLaplacian_pow
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
    (((n.factorial : K)⁻¹) • h3d K i ^ n) f ∈ FockLat R := by
  intro m
  rw [LinearMap.smul_apply, coeff_smul, smul_eq_mul, coeff_diagLaplacian_pow]
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h1 := hf (m + h3s i n)
  rw [xFactorial_add_diagExponent] at h1
  have : (xFact m : K) * ((n.factorial : K)⁻¹ * (coeff (m + h3s i n) f *
        ((((m (Sum.inl i) + n).descFactorial n : ℕ) : K) * (((m (Sum.inr i) + n).descFactorial n : ℕ) : K)))) =
      (((m (Sum.inr i) + n).choose n : ℕ) : K) *
        ((((m (Sum.inl i) + n).descFactorial n * xFact m : ℕ) : K) * coeff (m + h3s i n) f) := by
    rw [Nat.cast_mul, descFactorial_cast_eq (m (Sum.inr i))]
    field_simp
  rw [this]
  exact R.mul_mem (natCast_mem R _) h1
end Formalism.CountingSumsFrames
