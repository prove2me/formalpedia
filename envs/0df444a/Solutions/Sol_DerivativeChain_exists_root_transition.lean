-- Prove2me | solution 1 for DerivativeChain.exists_root_transition
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:45:57.78454+00:00
-- url     : https://prove2.me/submissions/492255e7-3a0b-4051-9e55-4a771c35ebe9

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



theorem rootProbability_nonneg (P : ℂ[X]) (z : ℂ) (w : P.roots.toFinset) :
    0 ≤ rootProbability P z w := by
  exact div_nonneg (P.derivRootWeight_nonneg z w)
    (Finset.sum_nonneg fun v _ => P.derivRootWeight_nonneg z v)

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

theorem rootProbability_support {P : ℂ[X]} (hP : 0 < P.degree)
    (w : P.roots.toFinset) : P.eval (w : ℂ) = 0 := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  exact (Polynomial.mem_roots hP0).mp (Multiset.mem_toFinset.mp w.property)





end DerivativeChain

namespace DerivativeChain
end DerivativeChain
open DerivativeChain in
theorem solution {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∃ π : P.roots.toFinset → ℝ,
      (∀ w, 0 ≤ π w) ∧
      (∑ w, π w = 1) ∧
      (∑ w, π w * (w : ℂ).re = z.re) ∧
      (∑ w, π w * (w : ℂ).im = z.im) ∧
      (∀ w : P.roots.toFinset, P.eval (w : ℂ) = 0) := by
  exact ⟨rootProbability P z, rootProbability_nonneg P z,
    sum_rootProbability hP z, rootProbability_mean_re hP hz,
    rootProbability_mean_im hP hz, rootProbability_support hP⟩
