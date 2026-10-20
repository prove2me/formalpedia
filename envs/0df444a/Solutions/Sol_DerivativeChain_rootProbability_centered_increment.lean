-- Prove2me | solution 1 for DerivativeChain.rootProbability_centered_increment
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:45:59.100817+00:00
-- url     : https://prove2.me/submissions/52b7ba48-8e52-4de5-84f2-c8e88c57fa43

import Definitions.Def_DerivativeChain_root_probability
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false

open scoped BigOperators Polynomial

noncomputable section

namespace DerivativeChain





theorem sum_rootProbability {P : ℂ[X]} (hP : 0 < P.degree) (z : ℂ) :
    ∑ w : P.roots.toFinset, rootProbability P z w = 1 := by
  classical
  simp only [rootProbability, ← Finset.sum_div, Finset.sum_coe_sort]
  exact div_self (Polynomial.sum_derivRootWeight_pos hP z).ne'

theorem rootProbability_mean {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∑ w : P.roots.toFinset, rootProbability P z w • (w : ℂ) = z := by
  classical
  simp only [rootProbability, div_eq_inv_mul, mul_smul, ← Finset.smul_sum]
  rw [Finset.sum_coe_sort P.roots.toFinset
    (fun w : ℂ => P.derivRootWeight z w • w)]
  exact (Polynomial.eq_centerMass_of_eval_derivative_eq_zero hP hz).symm

theorem rootProbability_mean_re {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∑ w : P.roots.toFinset, rootProbability P z w * (w : ℂ).re = z.re := by
  have h := congrArg Complex.reAddGroupHom (rootProbability_mean hP hz)
  simpa only [map_sum, Complex.coe_reAddGroupHom, Complex.smul_re, smul_eq_mul] using h

theorem rootProbability_mean_im {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∑ w : P.roots.toFinset, rootProbability P z w * (w : ℂ).im = z.im := by
  have h := congrArg Complex.imAddGroupHom (rootProbability_mean hP hz)
  simpa only [map_sum, Complex.coe_imAddGroupHom, Complex.smul_im, smul_eq_mul] using h







end DerivativeChain

namespace DerivativeChain
end DerivativeChain
open DerivativeChain in
theorem solution {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) (u : ℂ) :
    (∑ w : P.roots.toFinset, rootProbability P z w *
      ((z - u).re * ((w : ℂ) - z).re +
        (z - u).im * ((w : ℂ) - z).im)) = 0 := by
  have hre : (∑ w : P.roots.toFinset,
      rootProbability P z w * ((w : ℂ) - z).re) = 0 := by
    simp only [Complex.sub_re, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, rootProbability_mean_re hP hz,
      sum_rootProbability hP z, one_mul, sub_self]
  have him : (∑ w : P.roots.toFinset,
      rootProbability P z w * ((w : ℂ) - z).im) = 0 := by
    simp only [Complex.sub_im, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, rootProbability_mean_im hP hz,
      sum_rootProbability hP z, one_mul, sub_self]
  calc
    _ = (z - u).re * (∑ w : P.roots.toFinset,
          rootProbability P z w * ((w : ℂ) - z).re) +
        (z - u).im * (∑ w : P.roots.toFinset,
          rootProbability P z w * ((w : ℂ) - z).im) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = 0 := by rw [hre, him]; ring
