-- Prove2me | solution 1 for D1Bound5.finiteMTermEval_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:09:34.413683+00:00
-- url     : https://prove2.me/submissions/731192ed-f853-47b6-b553-2b707e49f6f7

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
namespace D1Bound5

private theorem finiteM_weight_monomial (B S C : ℝ) (p q r : ℕ)
    (hB : 1 ≤ B) (hBS : B ≤ S) (hC : 1 ≤ C)
    (hq : q ≤ 8) (hpq : p+q ≤ 11) (hr : r ≤ 2) :
    B^p*S^q*C^r ≤ B^3*S^8*C^2 := by
  have hS : 1 ≤ S := hB.trans hBS
  have hB0 : 0 ≤ B := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hanchor : B^p*S^q ≤ B^3*S^8 := by
    by_cases hp : p ≤ 3
    · exact mul_le_mul (pow_le_pow_right₀ hB hp)
        (pow_le_pow_right₀ hS hq) (pow_nonneg hS0 _) (pow_nonneg hB0 _)
    · have hp3 : 3 ≤ p := by omega
      have hrem : p-3+q ≤ 8 := by omega
      calc
        B^p*S^q = B^3*(B^(p-3)*S^q) := by
          conv_lhs => rw [show p=3+(p-3) by omega, pow_add]
          ring
        _ ≤ B^3*(S^(p-3)*S^q) := by gcongr
        _ = B^3*S^(p-3+q) := by rw [pow_add]
        _ ≤ B^3*S^8 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS hrem) (by positivity)
  exact mul_le_mul hanchor (pow_le_pow_right₀ hC hr)
    (pow_nonneg hC0 _) (by positivity)

/-- A single factored integer monomial has the advertised weighted height.
The admissibility condition is discharged for every actual term by a finite
natural-number certificate in FiniteMMatrix. -/
theorem _root_.solution (t : FiniteMTerm) (a b s v : ℂ)
    (B S C : ℝ) (hB : 1 ≤ B) (hBS : B ≤ S) (hC : 1 ≤ C)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hs : ‖s‖ ≤ S)
    (hv : ‖v‖ ≤ 2*S*C) (ht : finiteMTermAdmissible t) :
    ‖finiteMTermEval t a b s v‖ ≤ (finiteMTermWeight t : ℝ)*B^3*S^8*C^2 := by
  have hB0 : 0 ≤ B := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hab : ‖a-b‖ ≤ 2*B := (norm_sub_le a b).trans (by linarith)
  have has : ‖a-s‖ ≤ 2*S := (norm_sub_le a s).trans (by linarith)
  have hbs : ‖b-s‖ ≤ 2*S := (norm_sub_le b s).trans (by linarith)
  have hn : ‖(t.coeff : ℂ)‖ = (t.coeff.natAbs : ℝ) := by simp
  have hraw : ‖finiteMTermEval t a b s v‖ ≤
      (t.coeff.natAbs : ℝ)*B^t.ap*B^t.bp*S^t.sp*
        (2*B)^t.abp*(2*S)^t.asp*(2*S)^t.bsp*(2*S*C)^t.vp := by
    simp only [finiteMTermEval, norm_mul, norm_pow, hn]
    gcongr
  rcases ht with ⟨hq, hpq, hr⟩
  have hweight := finiteM_weight_monomial B S C
    (t.ap+t.bp+t.abp) (t.sp+t.asp+t.bsp+t.vp) t.vp
    hB hBS hC hq (by omega) hr
  calc
    _ ≤ _ := hraw
    _ = (finiteMTermWeight t : ℝ)*
        (B^(t.ap+t.bp+t.abp)*S^(t.sp+t.asp+t.bsp+t.vp)*C^t.vp) := by
      simp only [finiteMTermWeight, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        pow_add, mul_pow]
      ring
    _ ≤ (finiteMTermWeight t : ℝ)*(B^3*S^8*C^2) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = _ := by ring





end D1Bound5
end
