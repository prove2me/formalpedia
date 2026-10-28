-- Prove2me | solution 1 for D1Bound5.coherent_three_general_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:37.672408+00:00
-- url     : https://prove2.me/submissions/32152dcd-2a16-4eaa-a50e-2731dc3724ae

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherentQuotientForm_norm_le
import Theorems.Thm_D1Bound5_coherent_cpow_half_near_one_36
import Theorems.Thm_D1Bound5_coherent_three_general_scalar
import Theorems.Thm_D1Bound5_coherent_three_remainder_envelope

section
open Finset

namespace D1Bound5









/-- The general three-anchor estimate for the actual coherent form.
Only ordered anchor moduli and the manuscript's size conditions remain;
no auxiliary analytic approximation or remainder bound is assumed. -/
theorem _root_.solution
    (a : Fin 3 → ℂ) (p q eta : ℂ) (hinj : Function.Injective a)
    (hA : 0 < ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖) (hBS : ‖a 1‖ ≤ ‖a 2‖)
    (hP : 4 * ‖a 2‖ ≤ ‖p‖) (hAP : 9 ≤ ‖a 0‖ * ‖p‖)
    (hQ : ‖p‖ ≤ ‖q‖) (heta : eta ^ 2 = p * q) :
    ‖coherentQuotientForm a (coherentVandermonde3 a) p q eta‖ <
      5 * ‖a 1‖ * ‖a 2‖ ^ 2 / ‖coherentTerminalRoot p q eta‖ +
        3 * ‖a 2‖ * ‖coherentTerminalRoot p q eta‖ / (‖a 0‖ * ‖p‖ ^ 3) := by
  let A := ‖a 0‖
  let B := ‖a 1‖
  let S := ‖a 2‖
  let P := ‖p‖
  let Q := ‖q‖
  let E := ‖eta‖
  let Z := ‖coherentTerminalRoot p q eta‖
  let D := ‖coherentVandermonde3 a‖
  let f : ℂ := (1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ)
  let d := ‖1 - f‖
  have hB : 0 < B := hA.trans_le hAB
  have hS : 0 < S := hB.trans_le hBS
  have hP0 : 0 < P := by
    change 0 < ‖p‖
    have hs : 0 < ‖a 2‖ := hS
    nlinarith only [hP, hs]
  have hQ0 : 0 < Q := hP0.trans_le hQ
  have hp0 : p ≠ 0 := norm_pos_iff.mp hP0
  have hq0 : q ≠ 0 := norm_pos_iff.mp hQ0
  have heta0 : eta ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at heta
    exact (mul_ne_zero hp0 hq0) heta.symm
  have hE : 0 < E := norm_pos_iff.mpr heta0
  have hEsq : E ^ 2 = P * Q := by
    simpa only [E, P, Q, norm_pow, norm_mul] using congrArg norm heta
  have hPQ36 : (36 : ℝ) ≤ P * Q := by
    have hPA : 4 * A ≤ P := by dsimp [A, P]; linarith only [hAB, hBS, hP]
    have h1 := mul_le_mul_of_nonneg_right hPA hP0.le
    have h2 := mul_le_mul_of_nonneg_left hQ hP0.le
    nlinarith only [h1, h2, hAP]
  have hW : ‖p⁻¹ * q⁻¹‖ = 1 / (P * Q) := by
    simp [P, Q, norm_mul, norm_inv, one_div, mul_inv_rev, mul_comm]
  have hWsmall : ‖p⁻¹ * q⁻¹‖ ≤ (1 / 36 : ℝ) := by
    rw [hW]
    exact one_div_le_one_div_of_le (by norm_num) hPQ36
  have hnear := coherent_cpow_half_near_one_36 (p⁻¹ * q⁻¹)
    (mul_ne_zero (inv_ne_zero hp0) (inv_ne_zero hq0)) hWsmall
  have hZeq : Z = E * ‖f‖ := by simp only [Z, E, f, coherentTerminalRoot, norm_mul]
  have hZlo : (35 / 36 : ℝ) * E < Z := by
    rw [hZeq]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hnear.1 hE
  have hZhi : Z < (37 / 36 : ℝ) * E := by
    rw [hZeq]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hnear.2.1 hE
  have hZ : 0 < Z := by nlinarith only [hZlo, hE]
  have hd : d < 36 / (71 * P * Q) := by
    have h := hnear.2.2
    rw [hW] at h
    calc
      d < (36 / 71 : ℝ) * (1 / (P * Q)) := h
      _ = _ := by ring
  have ha : ∀ i, A ≤ ‖a i‖ := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact hAB
    · exact hAB.trans hBS
  have hp : ‖p⁻¹‖ ≤ 1 / P := by simp [P, norm_inv, one_div]
  have hq : ‖q⁻¹‖ ≤ 1 / P := by
    simpa only [Q, norm_inv, one_div] using one_div_le_one_div_of_le hP0 hQ
  have hDelta : coherentVandermonde3 a ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr (hinj.ne (by decide)))
        (sub_ne_zero.mpr (hinj.ne (by decide))))
      (sub_ne_zero.mpr (hinj.ne (by decide)))
  have hprod : (∏ i, ‖a i‖) = A * B * S := by
    simp [Fin.prod_univ_succ, A, B, S, mul_assoc]
  have hD : D ≤ 8 * B * S ^ 2 := by
    have h01 : ‖a 0 - a 1‖ ≤ 2 * B := by
      have h := norm_sub_le (a 0) (a 1)
      dsimp [B]
      linarith only [h, hAB]
    have h02 : ‖a 0 - a 2‖ ≤ 2 * S := by
      have h := norm_sub_le (a 0) (a 2)
      dsimp [S]
      linarith only [h, hAB, hBS]
    have h12 : ‖a 1 - a 2‖ ≤ 2 * S := by
      have h := norm_sub_le (a 1) (a 2)
      dsimp [S]
      linarith only [h, hBS]
    calc
      D = ‖a 0 - a 1‖ * ‖a 0 - a 2‖ * ‖a 1 - a 2‖ := by
        simp only [D, coherentVandermonde3, norm_mul]
      _ ≤ (2 * B) * (2 * S) * (2 * S) :=
        mul_le_mul (mul_le_mul h01 h02 (norm_nonneg _) (by positivity)) h12
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have henv := coherent_three_remainder_envelope p⁻¹ q⁻¹ A P hA hP0 hp hq hAP
  have hbound := coherentQuotientForm_norm_le a (by decide) hinj
    (coherentVandermonde3 a) p q eta hDelta heta0 A P hA hP0 ha hp hq (by linarith)
  have hL : ‖coherentQuotientForm a (coherentVandermonde3 a) p q eta‖ ≤
      D * E * (d + (1 / (3 * P ^ 3)) / (A * B * S)) := by
    rw [hprod] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_div_of_nonneg_right henv (by positivity)))
      (by positivity : 0 ≤ D * E))
  exact coherent_three_general_scalar A B S P Q E Z D d
    ‖coherentQuotientForm a (coherentVandermonde3 a) p q eta‖
    hA hB hS hP0 hQ0 hE hZ (norm_nonneg _) hD hEsq hZlo hZhi hd hL

end D1Bound5
end
