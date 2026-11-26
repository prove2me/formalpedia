-- Prove2me | solution 1 for FourierJacobi.Algebra.finiteCore_eq_closedCore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:32.264069+00:00
-- url     : https://prove2.me/submissions/66138c46-5a08-4ef7-9242-47e31936a40c

import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Theorems.Thm_FourierJacobi_Algebra_eight_weyl_sum_closed
import Theorems.Thm_FourierJacobi_Algebra_fifty_region_sum
import Theorems.Thm_FourierJacobi_Algebra_weylClosed_div_poincare


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K) (h : FiniteRegular t a b d) :
    finiteCore t a b d = closedCore t a b d := by
  have hterm (i : Fin 8) :
      weylWeights t a b i *
        (∑ j : Fin 50, regionTerms t d (weylU a b i) (weylV a b i) j) =
        weylTerms t a b d i := by
    rw [fifty_region_sum t d (weylU a b i) (weylV a b i)
      h.d_ne_zero (h.rows i).p (h.rows i).n (h.rows i).e (h.rows i).f (h.rows i).g]
    rfl
  have hD (i : Fin 8) : weylKernelDenominator t a b d i ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h.d_ne_zero) (h.rows i).p) (h.rows i).n
  calc
    finiteCore t a b d = (∑ i : Fin 8, weylTerms t a b d i) / poincare t := by
      unfold finiteCore
      congr 1
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = closedCore t a b d := by
      rw [eight_weyl_sum_closed t a b d h.a_ne_zero h.b_ne_zero h.d_ne_zero
        h.a_ne_one h.b_ne_one h.a_ne_b h.ab_ne_one hD h.common]
      exact weylClosed_div_poincare t a b d
end FourierJacobi.Algebra
