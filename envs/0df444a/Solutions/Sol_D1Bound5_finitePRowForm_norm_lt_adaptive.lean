-- Prove2me | solution 1 for D1Bound5.finitePRowForm_norm_lt_adaptive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:40:15.155966+00:00
-- url     : https://prove2.me/submissions/92fe0504-9c4c-4db7-9181-0398df39d9ac

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_FinitePHeight_Definitions
import Definitions.Def_D1Bound5_FinitePIntegralRows_Definitions
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions
import Theorems.Thm_D1Bound5_finitePRowForm_eq_root_sum
import Theorems.Thm_D1Bound5_finiteP_height_scaled
import Theorems.Thm_D1Bound5_finiteP_residual_norm_le_adaptive
import Theorems.Thm_D1Bound5_finite_row_root_transfer_norm_lt_of_height

section
namespace D1Bound5

theorem _root_.solution (a b s c z rA rB rS : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (hz : z ≠ 0)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hC : 200 ≤ ‖c‖) (hAC : 1000 ≤ ‖a‖*‖c‖)
    (q : ℝ) (hq : 1 ≤ q) (hqab : q*‖a‖ ≤ ‖b‖)
    (herr : ∀ j : Fin 3,
      ‖(1+1/(![a,b,s] j*c))^(1/2 : ℂ)-![rA,rB,rS] j/(![a,b,s] j*z)‖ ≤
        (101/100 : ℝ)*‖c‖/(‖![a,b,s] j‖*‖z‖^2)) (i : Fin 4) :
    ‖finitePRowForm a b s c z rA rB rS i‖ <
      2400*max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2)*‖c‖^3/‖z‖+
        finitePAdaptiveRate (1/q)*‖s‖^2*‖z‖/(‖a‖^3*‖c‖^5) := by
  have hC0 : 0 < ‖c‖ := by linarith only [hC]
  have hanchor (j : Fin 3) : ![a,b,s] j ≠ 0 := by fin_cases j <;> assumption
  have hh := finiteP_height_scaled a b s c hA hAB hBS hC i
  have hheight : (∑ j : Fin 3, ‖finitePRootColumn a b s c i j‖) <
      (2400*max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2)*‖c‖^2)/(101/100 : ℝ) := by
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<101/100)).mpr
    nlinarith only [hh]
  have hres := finiteP_residual_norm_le_adaptive a b s c hA hAB hBS hAC q hq hqab i
  have h := finite_row_root_transfer_norm_lt_of_height (finitePDividedMatrix a b s c i 0) z
    ![a,b,s] (finitePRootColumn a b s c i)
    (fun j => (1+1/(![a,b,s] j*c))^(1/2 : ℂ)) ![rA,rB,rS]
    hanchor hz ((101/100 : ℝ)*‖c‖)
    ((2400*max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2)*‖c‖^2)/(101/100 : ℝ))
    (finitePAdaptiveRate (1/q)*‖s‖^2/(‖a‖^3*‖c‖^5)) (by positivity) herr hheight
    (by simpa only [finitePResidual,finitePRootColumn] using hres)
  rw [finitePRowForm_eq_root_sum]
  convert h using 1 <;> ring

end D1Bound5
end
