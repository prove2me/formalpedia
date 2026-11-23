-- Prove2me | solution 1 for Formalism.CountingSumsFrames.coeff_diagLaplacian_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:38.573131+00:00
-- url     : https://prove2.me/submissions/fe00bd2c-4981-4df1-846a-418bd33b0756

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_diagExponent_inl
import Theorems.Thm_Formalism_CountingSumsFrames_diagExponent_inr
import Theorems.Thm_Formalism_CountingSumsFrames_diagLaplacian_apply

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
theorem _root_.solution (i : Fin k) (n : ℕ) : ∀ (f : PolXY K k) (m : XY k →₀ ℕ),
    coeff m ((h3d K i ^ n) f) = coeff (m + h3s i n) f *
      (((m (Sum.inl i) + n).descFactorial n : ℕ) * ((m (Sum.inr i) + n).descFactorial n : ℕ)) := by
  induction n with
  | zero => intro f m; simp [h3s]
  | succ n ih =>
    intro f m
    rw [pow_succ, Module.End.mul_apply, ih]
    have h1 : coeff (m + h3s i n) (h3d K i f) = coeff (m + h3s i (n + 1)) f *
        (((m (Sum.inl i) + n + 1 : ℕ) : K) * ((m (Sum.inr i) + n + 1 : ℕ) : K)) := by
      simp only [diagLaplacian_apply, coeff_pderiv]
      have e : m + h3s i n + Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1 = m + h3s i (n + 1) := by
        simp only [h3s, Finsupp.single_add]
        abel
      rw [e]
      simp [diagExponent_inl, diagExponent_inr]
      ring
    rw [h1, ← add_assoc, ← add_assoc, Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ]
    push_cast
    ring
end Formalism.CountingSumsFrames
