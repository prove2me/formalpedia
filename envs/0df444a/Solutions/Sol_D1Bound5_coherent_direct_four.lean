-- Prove2me | solution 1 for D1Bound5.coherent_direct_four
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:10:53.157782+00:00
-- url     : https://prove2.me/submissions/04bd83bd-52de-4cdb-855b-65a93478f0d0

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
import Theorems.Thm_D1Bound5_coherentVandermonde4_norm_le
import Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq
import Theorems.Thm_D1Bound5_coherent_four_parameter_form_bounds

section
open Finset

namespace D1Bound5



/-- The complete direct-four lemma for actual coherent roots. -/
theorem _root_.solution
    (a : Fin 4 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ)
    (hA : 1 ≤ ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖)
    (hBS : ‖a 1‖ ≤ ‖a 2‖) (hST : ‖a 2‖ ≤ ‖a 3‖)
    (hTP : ‖a 3‖ ≤ ‖p‖) (hP : 1000 ≤ ‖p‖) (hQ : 1000*‖p‖ ≤ ‖q‖)
    (heta : eta^2 = p*q) :
    ‖coherentQuotientForm a (coherentVandermonde4 a) p q eta‖ <
        13*‖a 1‖*‖a 2‖^2*‖a 3‖^3/‖coherentTerminalRoot p q eta‖ +
          49*‖a 2‖*‖a 3‖^2*‖coherentTerminalRoot p q eta‖/(50*‖a 0‖*‖p‖^4) ∧
      (coherentQuotientForm a (coherentVandermonde4 a) p q eta = 0 →
        10*‖a 0‖*‖a 1‖*‖a 2‖*‖a 3‖*‖p‖^3 < ‖q‖ ∧
          ‖q‖ < 17*‖a 0‖*‖a 1‖*‖a 2‖*‖a 3‖*‖p‖^3) := by
  let A := ‖a 0‖
  let B := ‖a 1‖
  let S := ‖a 2‖
  let T := ‖a 3‖
  let P := ‖p‖
  let Z := ‖coherentTerminalRoot p q eta‖
  let D := ‖coherentVandermonde4 a‖
  have hA0 : 0 < A := by dsimp [A]; linarith only [hA]
  have hB0 : 0 < B := hA0.trans_le hAB
  have hS0 : 0 < S := hB0.trans_le hBS
  have hT0 : 0 < T := hS0.trans_le hST
  have hP0 : 0 < P := by dsimp [P]; linarith only [hP]
  have hQ0 : 0 < ‖q‖ := by nlinarith only [hP,hQ]
  have hAP : 1000 ≤ A*P := by
    have h := mul_le_mul hA hP (by norm_num : (0:ℝ)≤1000) hA0.le
    nlinarith only [h]
  have hPQ : 10000 < P*‖q‖ := by
    have hq : 1000 ≤ ‖q‖ := by nlinarith only [hP,hQ]
    have h := mul_le_mul hP hq (by norm_num : (0:ℝ)≤1000) hP0.le
    nlinarith only [h]
  have ha : ∀ i, A ≤ ‖a i‖ := by intro i; fin_cases i <;> dsimp [A] <;> linarith
  have h := coherent_four_parameter_form_bounds a hinj p q eta A hA0 ha hP0 hQ hPQ hAP heta
  have hprod : (∏ i, ‖a i‖) = A*B*S*T := by
    simp [Fin.prod_univ_succ,A,B,S,T,mul_assoc]
  rw [hprod] at h
  have hD : D ≤ 24*B*S^2*T^3 := coherentVandermonde4_norm_le a hAB hBS hST
  have hZ : 0 < Z := by
    apply norm_pos_iff.mpr
    intro hz
    have hs := coherent_analytic_terminal_root_sq p q eta (norm_pos_iff.mp hP0) (norm_pos_iff.mp hQ0) heta
    change (coherentTerminalRoot p q eta)^2 = p*q+1 at hs
    rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at hs
    have hn : ‖p‖*‖q‖ = 1 := by
      have heq : p*q = -1 := by linear_combination -hs
      simpa only [norm_mul,norm_neg,norm_one] using congrArg norm heq
    nlinarith only [hn,hPQ]
  have hfirst : 51*D/(100*Z) ≤ 13*B*S^2*T^3/Z := by
    calc
      _ ≤ 51*(24*B*S^2*T^3)/(100*Z) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by norm_num)) (by positivity)
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity) hZ).2
        nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hB0.le (sq_nonneg S))
          (pow_nonneg hT0.le 3)) hZ.le]
  have hsecond : (49/1200 : ℝ)*D*Z/((A*B*S*T)*P^4) ≤
      49*S*T^2*Z/(50*A*P^4) := by
    calc
      _ ≤ (49/1200 : ℝ)*(24*B*S^2*T^3)*Z/((A*B*S*T)*P^4) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hD (by norm_num)) hZ.le
      _ = _ := by field_simp; ring
  refine ⟨h.1.trans_le (add_le_add hfirst hsecond), ?_⟩
  intro hzero
  have hw := h.2 hzero
  constructor <;> nlinarith only [hw.1,hw.2]

end D1Bound5
end
