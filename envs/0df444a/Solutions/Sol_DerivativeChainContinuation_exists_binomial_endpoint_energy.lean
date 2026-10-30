-- Prove2me | solution 1 for DerivativeChainContinuation.exists_binomial_endpoint_energy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:54:04.282999+00:00
-- url     : https://prove2.me/submissions/2dd893ec-c793-4787-b5ea-22fdf01b17e9

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainPrivate_exists_nonpos_of_probability_mean_zero
import Theorems.Thm_DerivativeChainPrivate_rootProbability_energy_defect
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







theorem rootProbability_support {P : ℂ[X]} (hP : 0 < P.degree)
    (w : P.roots.toFinset) : P.eval (w : ℂ) = 0 := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  exact (Polynomial.mem_roots hP0).mp (Multiset.mem_toFinset.mp w.property)





end DerivativeChain



open scoped BigOperators Polynomial

noncomputable section

namespace DerivativeChainPrivate





/-- Every critical point of a nonconstant complex polynomial admits an actual
predecessor root whose squared step is bounded by the increase of squared norm.
This is the one-step inequality that telescopes along a derivative-root chain. -/
theorem exists_root_energy (P : Polynomial ℂ) (hP : 0 < P.degree)
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

end DerivativeChainPrivate




end
end


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial



end DerivativeChainContinuation

theorem solution (q : ℕ) (hq : 2 ≤ q) (c u : ℂ) :
    ∃ b : ℂ, b^q= -c ∧ ‖b‖^2 ≤ ‖u+b‖^2-‖u‖^2 := by
  let F : Polynomial ℂ := (X-C u)^q+C c
  have hd : F.natDegree=q := by
    simp [F,natDegree_add_C,natDegree_pow]
  have hdeg : 0 < F.degree := natDegree_pos_iff_degree_pos.mp (by omega)
  have hcrit : F.derivative.eval u=0 := by
    simp [F,derivative_pow,show q-1 ≠ 0 by omega]
  obtain ⟨v,hv,he⟩ := DerivativeChainPrivate.exists_root_energy F hdeg u hcrit
  refine ⟨v-u,?_,?_⟩
  · simp only [F,eval_add,eval_pow,eval_sub,eval_X,eval_C] at hv
    linear_combination hv
  · simpa only [show u+(v-u)=v by ring] using he
