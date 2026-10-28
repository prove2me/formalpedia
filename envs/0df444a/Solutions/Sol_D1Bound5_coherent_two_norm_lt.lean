-- Prove2me | solution 1 for D1Bound5.coherent_two_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:12.915427+00:00
-- url     : https://prove2.me/submissions/c6d49923-fac1-43ba-a9c3-82aedf8add8b

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
import Definitions.Def_D1Bound5_CoherentFormBounds_Definitions
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherentQuotientForm_normalized_eq
import Theorems.Thm_D1Bound5_coherentRemainder_two_norm_le
import Theorems.Thm_D1Bound5_coherent_cpow_half_near_one
import Theorems.Thm_D1Bound5_coherent_half_binomial_manuscript_anchor_radius
import Theorems.Thm_D1Bound5_coherent_two_upper_scalar

section
open Finset

namespace D1Bound5









/-- The manuscript's quantitative two-anchor upper estimate for the
actual coherent quotient form and its actual terminal square root.
The tail and branch estimates are proved internally. -/
theorem _root_.solution
    (a : Fin 2 → ℂ) (p q eta : ℂ) (hinj : Function.Injective a)
    (hA : 0 < ‖a 0‖) (hP : 0 < ‖p‖) (hAB : ‖a 0‖ ≤ ‖a 1‖)
    (hAP : 32 ≤ ‖a 0‖ * ‖p‖) (hQ : 4 * ‖p‖ ≤ ‖q‖)
    (hPQ : 10000 < ‖p‖ * ‖q‖) (heta : eta ^ 2 = p * q) :
    ‖coherentQuotientForm a (a 0 - a 1) p q eta‖ <
      21 * ‖a 1‖ / (20 * ‖coherentTerminalRoot p q eta‖) +
        ‖coherentTerminalRoot p q eta‖ / (2 * ‖a 0‖ * ‖p‖ ^ 2) := by
  let A := ‖a 0‖
  let B := ‖a 1‖
  let P := ‖p‖
  let Q := ‖q‖
  let E := ‖eta‖
  let Z := ‖coherentTerminalRoot p q eta‖
  let f : ℂ := (1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ)
  let d := ‖1 - f‖
  let F := ‖coherentRemainder a p q‖
  have hB : 0 < B := hA.trans_le hAB
  have hQ0 : 0 < Q := by dsimp [Q]; nlinarith only [hP, hQ]
  have hp0 : p ≠ 0 := norm_pos_iff.mp hP
  have hq0 : q ≠ 0 := norm_pos_iff.mp hQ0
  have heta0 : eta ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at heta
    exact (mul_ne_zero hp0 hq0) heta.symm
  have hE : 0 < E := norm_pos_iff.mpr heta0
  have hEsq : E ^ 2 = P * Q := by
    simpa only [E, P, Q, norm_pow, norm_mul] using congrArg norm heta
  have hW : ‖p⁻¹ * q⁻¹‖ = 1 / (P * Q) := by
    simp [P, Q, norm_mul, norm_inv, one_div, mul_inv_rev, mul_comm]
  have hWsmall : ‖p⁻¹ * q⁻¹‖ < (1 / 10000 : ℝ) := by
    rw [hW]
    exact one_div_lt_one_div_of_lt (by norm_num) hPQ
  have hnear := coherent_cpow_half_near_one (p⁻¹ * q⁻¹)
    (mul_ne_zero (inv_ne_zero hp0) (inv_ne_zero hq0)) hWsmall
  have hZeq : Z = E * ‖f‖ := by simp only [Z, E, f, coherentTerminalRoot, norm_mul]
  have hZlo : (99 / 100 : ℝ) * E < Z := by
    rw [hZeq]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hnear.1 hE
  have hZhi : Z < (101 / 100 : ℝ) * E := by
    rw [hZeq]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hnear.2.1 hE
  have hZ : 0 < Z := by nlinarith only [hZlo, hE]
  have hd : d < 100 / (199 * P * Q) := by
    have h := hnear.2.2.2
    rw [hW] at h
    calc
      d < (100 / 199 : ℝ) * (1 / (P * Q)) := h
      _ = _ := by ring
  have ha : ∀ i, A ≤ ‖a i‖ := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact hAB
  have han : ∀ i, a i ≠ 0 := fun i => norm_pos_iff.mp (hA.trans_le (ha i))
  have hp : ‖p⁻¹‖ ≤ 1 / P := by simp [P, norm_inv, one_div]
  have hq : ‖q⁻¹‖ ≤ 1 / (4 * P) := by
    simpa only [Q, norm_inv, one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < 4 * P) hQ
  have hq' : ‖q⁻¹‖ ≤ 1 / P :=
    hq.trans (one_div_le_one_div_of_le hP (by dsimp [P]; nlinarith only [hP]))
  have hF : F ≤ 7 / (32 * P ^ 2) :=
    coherentRemainder_two_norm_le a p q A P hA hP ha hp hq hAP
  have hDelta : a 0 - a 1 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have hxp : ∀ i, ‖p⁻¹ * (a i)⁻¹‖ < 1 := by
    intro i
    exact coherent_half_binomial_manuscript_anchor_radius Finset.univ a p⁻¹ A P
      hA hP (fun j _ => ha j) hp (by linarith) i (Finset.mem_univ i)
  have hxq : ∀ i, ‖q⁻¹ * (a i)⁻¹‖ < 1 := by
    intro i
    exact coherent_half_binomial_manuscript_anchor_radius Finset.univ a q⁻¹ A P
      hA hP (fun j _ => ha j) hq' (by linarith) i (Finset.mem_univ i)
  have hexact := coherentQuotientForm_normalized_eq a (by decide) han hinj
    (a 0 - a 1) p q eta hDelta heta0 hxp hxq
  have hmul : coherentQuotientForm a (a 0 - a 1) p q eta =
      ((a 0 - a 1) * eta) *
        (1 - f + (-1 * (a 0 * a 1)⁻¹) * coherentRemainder a p q) := by
    have h := (div_eq_iff (mul_ne_zero hDelta heta0)).mp hexact
    simpa [Fin.prod_univ_two, f, mul_comm] using h
  have hc : ‖(-1 : ℂ) * (a 0 * a 1)⁻¹‖ = 1 / (A * B) := by
    simp [A, B, norm_mul, norm_inv, one_div, mul_inv_rev, mul_comm]
  have hL : ‖coherentQuotientForm a (a 0 - a 1) p q eta‖ ≤
      ‖a 0 - a 1‖ * E * (d + F / (A * B)) := by
    rw [hmul, norm_mul, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ ‖a 0 - a 1‖ * E)
    calc
      _ ≤ ‖1 - f‖ + ‖(-1 * (a 0 * a 1)⁻¹) * coherentRemainder a p q‖ :=
        norm_add_le _ _
      _ = d + F / (A * B) := by rw [norm_mul, hc]; dsimp [d, F]; ring
  have hD : ‖a 0 - a 1‖ ≤ 2 * B := by
    have h := norm_sub_le (a 0) (a 1)
    dsimp [B]
    linarith
  exact coherent_two_upper_scalar A B P Q E Z ‖a 0 - a 1‖ d F
    ‖coherentQuotientForm a (a 0 - a 1) p q eta‖
    hA hB hP hQ0 hE hZ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hD hEsq hZlo hZhi hd hF hL

end D1Bound5
end
