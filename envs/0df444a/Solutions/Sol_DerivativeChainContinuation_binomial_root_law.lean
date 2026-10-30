-- Prove2me | solution 1 for DerivativeChainContinuation.binomial_root_law
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:54:22.144257+00:00
-- url     : https://prove2.me/submissions/c3eaee0b-7811-41c9-a4f4-5273c166c0dc

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false




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





theorem rootProbability_support {P : ℂ[X]} (hP : 0 < P.degree)
    (w : P.roots.toFinset) : P.eval (w : ℂ) = 0 := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  exact (Polynomial.mem_roots hP0).mp (Multiset.mem_toFinset.mp w.property)





end DerivativeChain



open scoped BigOperators Polynomial

noncomputable section

namespace DerivativeChainPrivate







end DerivativeChainPrivate




end
end


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



end DerivativeChainContinuation

theorem solution (q : ℕ) (hq : 2 ≤ q) (c : ℂ) :
    let F : Polynomial ℂ := X^q+C c;
    ∃ π : F.roots.toFinset → ℝ,
      (∀ i, 0 ≤ π i) ∧ (∑ i, π i=1) ∧ (∑ i, (π i:ℂ)*(i:ℂ)=0) ∧
      (∀ i : F.roots.toFinset, (i:ℂ)^q= -c) ∧
      (∀ i : F.roots.toFinset, ‖(i:ℂ)‖=‖c‖^((q:ℝ)⁻¹)) := by
  let F : Polynomial ℂ := X^q+C c
  have hd : F.natDegree=q := by simp [F]
  have hdeg : 0 < F.degree := natDegree_pos_iff_degree_pos.mp (by omega)
  have hcrit : F.derivative.eval 0=0 := by simp [F,derivative_X_pow,show q-1 ≠ 0 by omega]
  let π := DerivativeChain.rootProbability F 0
  have hp (i : F.roots.toFinset) : (i:ℂ)^q= -c := by
    have hh := DerivativeChain.rootProbability_support hdeg i
    simp only [F,eval_add,eval_pow,eval_X,eval_C] at hh
    linear_combination hh
  refine ⟨π,DerivativeChain.rootProbability_nonneg F 0,
    DerivativeChain.sum_rootProbability hdeg 0,?_,hp,?_⟩
  · simpa only [Complex.real_smul] using DerivativeChain.rootProbability_mean hdeg hcrit
  · intro i
    have hn := congrArg norm (hp i)
    simp only [norm_pow,norm_neg] at hn
    have hr := Real.rpow_inv_natCast_pow (norm_nonneg c) (show q ≠ 0 by omega)
    apply (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg c) _) (show q ≠ 0 by omega)).mp
    exact hn.trans hr.symm
