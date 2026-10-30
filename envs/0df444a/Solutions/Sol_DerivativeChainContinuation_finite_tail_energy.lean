-- Prove2me | solution 1 for DerivativeChainContinuation.finite_tail_energy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:55:59.009247+00:00
-- url     : https://prove2.me/submissions/ec8632fa-e71c-423e-a032-60a216b83c0b

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
open scoped BigOperators



end DerivativeChainContinuation

theorem solution (P : ℕ → Polynomial ℂ) (h : ℕ)
    (hdegree : ∀ j < h, 0 < (P (j+1)).degree)
    (hstep : ∀ j < h, ∀ w : ℂ, (P j).eval w=0 → (P (j+1)).derivative.eval w=0)
    (b : ℂ) (hb : (P 0).eval b=0) :
    ∃ z : ℕ → ℂ, z 0=b ∧ (∀ j ≤ h, (P j).eval (z j)=0) ∧
      (∑ j ∈ Finset.range h, ‖z (j+1)-z j‖^2) ≤ ‖z h‖^2-‖b‖^2 := by
  classical
  let next (j : ℕ) (w : ℂ) := Classical.epsilon (fun v : ℂ =>
    (P (j+1)).eval v=0 ∧ ‖v-w‖^2 ≤ ‖v‖^2-‖w‖^2)
  have hn (j : ℕ) (hj : j < h) (w : ℂ) (hw : (P j).eval w=0) :
      (P (j+1)).eval (next j w)=0 ∧ ‖next j w-w‖^2 ≤ ‖next j w‖^2-‖w‖^2 := by
    dsimp only [next]
    apply Classical.epsilon_spec (p := fun v : ℂ =>
      (P (j+1)).eval v=0 ∧ ‖v-w‖^2 ≤ ‖v‖^2-‖w‖^2)
    apply DerivativeChainPrivate.exists_root_energy (P (j+1)) (hdegree j hj) w
    exact hstep j hj w hw
  let z : ℕ → ℂ := Nat.rec b (fun j w => next j w)
  have hz0 : z 0=b := rfl
  have hzs (j : ℕ) : z (j+1)=next j (z j) := rfl
  have hzroot (j : ℕ) (hj : j ≤ h) : (P j).eval (z j)=0 := by
    induction j with
    | zero => exact hb
    | succ j ih =>
      rw [hzs]
      exact (hn j (by omega) (z j) (ih (by omega))).1
  refine ⟨z,hz0,hzroot,?_⟩
  calc
    _ ≤ ∑ j ∈ Finset.range h, (‖z (j+1)‖^2-‖z j‖^2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simpa only [hzs] using (hn j hj' (z j) (hzroot j (by omega))).2
    _ = _ := by rw [Finset.sum_range_sub (fun j => ‖z j‖^2),hz0]
