-- Prove2me | solution 1 for D1Bound5.coherent_three_separated_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:39:22.697338+00:00
-- url     : https://prove2.me/submissions/98912306-5d6b-46ac-8d05-587bbbab3e31

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq
import Theorems.Thm_D1Bound5_coherent_three_parameter_form_bounds
import Theorems.Thm_D1Bound5_coherent_three_vandermonde_ratio_bounds

section
open Finset

namespace D1Bound5

/-- The separated three-anchor row at parameter 1000. All constants
are exact rational consequences of the proved binomial tail. -/
theorem coherent_three_parameter_1000 :
    0 < coherentThreeLowerConstant 1000 ∧
      0 < coherentThreeUpperConstant 1000 ∧
      100*coherentThreeUpperConstant 1000/99 < (3/32 : ℝ) ∧
      5 < 100/(201*coherentThreeUpperConstant 1000) ∧
      100/(199*coherentThreeLowerConstant 1000) < 15 := by
  norm_num [coherentThreeLowerConstant,coherentThreeUpperConstant,coherentThreeTailConstant]

/-- The stronger three-anchor estimate used for the V window. The
factor 3/4 comes from terminal separation and the parameter-1000 tail. -/
theorem _root_.solution
    (a : Fin 3 → ℂ) (p q eta : ℂ) (hinj : Function.Injective a)
    (hA : 0 < ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖) (hBS : ‖a 1‖ ≤ ‖a 2‖)
    (hP : 0 < ‖p‖) (hAP : 1000 ≤ ‖a 0‖*‖p‖)
    (hQ : 4*‖p‖ ≤ ‖q‖) (hPQ : 10000 < ‖p‖*‖q‖)
    (heta : eta^2 = p*q) :
    ‖coherentQuotientForm a (coherentVandermonde3 a) p q eta‖ <
      5*‖a 1‖*‖a 2‖^2/‖coherentTerminalRoot p q eta‖ +
        3*‖a 2‖*‖coherentTerminalRoot p q eta‖/(4*‖a 0‖*‖p‖^3) ∧
    (coherentQuotientForm a (coherentVandermonde3 a) p q eta = 0 →
      5*‖a 0‖*‖a 1‖*‖a 2‖*‖p‖^2 < ‖q‖ ∧
        ‖q‖ < 15*‖a 0‖*‖a 1‖*‖a 2‖*‖p‖^2) := by
  have hB : 0 < ‖a 1‖ := hA.trans_le hAB
  have hS : 0 < ‖a 2‖ := hB.trans_le hBS
  have hq : 0 < ‖q‖ := by linarith only [hQ,hP]
  have ha : ∀ i, ‖a 0‖ ≤ ‖a i‖ := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact hAB
    · exact hAB.trans hBS
  have hc := coherent_three_parameter_1000
  have hb := coherent_three_parameter_form_bounds a hinj p q eta
    ‖a 0‖ 1000 (3/32) 15 hA ha hP hQ hPQ (by norm_num) hAP heta
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  have hprod : (∏ i, ‖a i‖) = ‖a 0‖*‖a 1‖*‖a 2‖ := by
    simp [Fin.prod_univ_succ,mul_assoc]
  rw [hprod] at hb
  have hZ : 0 < ‖coherentTerminalRoot p q eta‖ := by
    have hs := coherent_analytic_terminal_root_sq p q eta
      (norm_pos_iff.mp hP) (norm_pos_iff.mp hq) heta
    have hlo := norm_sub_le (p*q+1) (1 : ℂ)
    simp only [add_sub_cancel_right,norm_mul,norm_one] at hlo
    have hn : ‖coherentTerminalRoot p q eta‖^2 = ‖p*q+1‖ := by
      simpa only [coherentTerminalRoot, norm_pow] using congrArg norm hs
    have hz := norm_nonneg (coherentTerminalRoot p q eta)
    nlinarith only [hlo,hPQ,hn,hz]
  have hD := (coherent_three_vandermonde_ratio_bounds a hinj hA hAB hBS).2
  have hD' : ‖coherentVandermonde3 a‖ ≤ 8*‖a 1‖*‖a 2‖^2 := by
    have hh := (div_le_iff₀ (by positivity : 0 < ‖a 1‖*‖a 2‖^2)).1 hD
    nlinarith only [hh]
  constructor
  · apply hb.1.trans_le
    have hfirst : 51*‖coherentVandermonde3 a‖/(100*‖coherentTerminalRoot p q eta‖) ≤
        5*‖a 1‖*‖a 2‖^2/‖coherentTerminalRoot p q eta‖ := by
      apply (div_le_div_iff₀ (by positivity) hZ).2
      have hh := mul_le_mul_of_nonneg_right hD' hZ.le
      have hp : 0 ≤ ‖a 1‖*‖a 2‖^2*‖coherentTerminalRoot p q eta‖ := by positivity
      nlinarith only [hh,hp]
    have hsecond : (3/32 : ℝ)*‖coherentVandermonde3 a‖*‖coherentTerminalRoot p q eta‖/
          (‖a 0‖*‖a 1‖*‖a 2‖*‖p‖^3) ≤
        3*‖a 2‖*‖coherentTerminalRoot p q eta‖/(4*‖a 0‖*‖p‖^3) := by
      calc
        _ ≤ (3/32 : ℝ)*(8*‖a 1‖*‖a 2‖^2)*‖coherentTerminalRoot p q eta‖/
            (‖a 0‖*‖a 1‖*‖a 2‖*‖p‖^3) := by gcongr
        _ = _ := by field_simp; ring
    exact add_le_add hfirst hsecond
  · intro hzero
    simpa only [mul_assoc] using hb.2 hzero

end D1Bound5
end
