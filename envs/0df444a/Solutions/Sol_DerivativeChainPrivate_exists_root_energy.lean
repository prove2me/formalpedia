-- Prove2me | solution 1 for DerivativeChainPrivate.exists_root_energy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:47:30.530926+00:00
-- url     : https://prove2.me/submissions/564a5d9c-1437-4516-a31f-fbd550f68f11

import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainPrivate_exists_nonpos_of_probability_mean_zero
import Theorems.Thm_DerivativeChainPrivate_rootProbability_energy_defect
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







theorem rootProbability_support {P : ℂ[X]} (hP : 0 < P.degree)
    (w : P.roots.toFinset) : P.eval (w : ℂ) = 0 := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  exact (Polynomial.mem_roots hP0).mp (Multiset.mem_toFinset.mp w.property)





end DerivativeChain

namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate in
theorem solution (P : Polynomial ℂ) (hP : 0 < P.degree)
    (z : ℂ) (hz : P.derivative.eval z = 0) :
    ∃ a : ℂ, P.eval a = 0 ∧ ‖a - z‖ ^ 2 ≤ ‖a‖ ^ 2 - ‖z‖ ^ 2 := by
  obtain ⟨w, hw⟩ := exists_nonpos_of_probability_mean_zero
    (DerivativeChain.rootProbability P z)
    (fun w : P.roots.toFinset => ‖(w : ℂ) - z‖ ^ 2 - ‖(w : ℂ)‖ ^ 2 + ‖z‖ ^ 2)
    (DerivativeChain.rootProbability_nonneg P z)
    (DerivativeChain.sum_rootProbability hP z)
    (rootProbability_energy_defect P hP z hz)
  refine ⟨w, DerivativeChain.rootProbability_support hP w, ?_⟩
  linarith
