-- Prove2me | solution 1 for DerivativeChainPrefixLaws.source_uniform_variance_controlled_tower
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:46:15.765722+00:00
-- url     : https://prove2.me/submissions/22bf4626-09a1-49b0-a8b7-6e5a34436d61

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Theorems.Thm_DerivativeChainContinuation_uniform_polynomial_tower
import Theorems.Thm_DerivativeChainPrefixLaws_scaled_sequence_contraction
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_centroid
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_variance_contraction
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
noncomputable section



theorem uniform_row_centroid (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (h : ℕ) (hh : h ≤ n) :
    complexCentroid (r h)=r 0 0 := by
  induction h with
  | zero => simp [complexCentroid]
  | succ h ih =>
    rw [uniform_step_centroid r h (hstep h (by omega)),ih (by omega)]









theorem uniform_tower_variance_contraction (r : ComplexRootRows) (n h : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (hh : h ≤ n) :
    (n:ℝ)*(∑ j : Fin (h+1), (h+1:ℝ)⁻¹*‖r h j-r 0 0‖^2) ≤
      (h:ℝ)*(∑ j : Fin (n+1), (n+1:ℝ)⁻¹*‖r n j-r 0 0‖^2) := by
  have hs (k : ℕ) (hk : k<n) :
      (k+1:ℝ)*secondMoment (fun j : Fin (k+1) => r k j-r 0 0) ≤
        (k:ℝ)*secondMoment (fun i : Fin (k+2) => r (k+1) i-r 0 0) :=
    uniform_step_variance_contraction r k (hstep k hk) (r 0 0)
      (uniform_row_centroid r n hstep (k+1) (by omega))
  have H := scaled_sequence_contraction
    (fun k => secondMoment (fun i : Fin (k+1) => r k i-r 0 0)) n h hh hs
  simpa only [secondMoment,Complex.normSq_eq_norm_sq,div_eq_mul_inv,
    Finset.mul_sum,Finset.sum_mul,mul_comm,Nat.cast_add,Nat.cast_one] using H

theorem uniform_tower_variance_contraction_div (r : ComplexRootRows) (n h : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (hh : h ≤ n) :
    (∑ j : Fin (h+1), (h+1:ℝ)⁻¹*‖r h j-r 0 0‖^2) ≤
      (h:ℝ)/(n:ℝ)*(∑ j : Fin (n+1), (n+1:ℝ)⁻¹*‖r n j-r 0 0‖^2) := by
  by_cases hn : n=0
  · subst n
    have he : h=0 := by omega
    subst h
    simp
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hnR).2
  simpa only [mul_comm] using uniform_tower_variance_contraction r n h hstep hh

end
end DerivativeChainPrefixLaws


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainPrefixLaws






theorem solution (n : ℕ) (a : Fin (n+1) → ℂ) :
    ∃ r : _root_.DerivativeChainContinuation.ComplexRootRows, r n=a ∧ (∀ k<n, _root_.DerivativeChainContinuation.UniformPolynomialStep r k) ∧
      r 0 0=_root_.DerivativeChainContinuation.complexCentroid a ∧
      ∀ h≤n, (∑ j : Fin (h+1), (h+1:ℝ)⁻¹*‖r h j-_root_.DerivativeChainContinuation.complexCentroid a‖^2) ≤
        (h:ℝ)/(n:ℝ)*(∑ j : Fin (n+1), (n+1:ℝ)⁻¹*‖a j-_root_.DerivativeChainContinuation.complexCentroid a‖^2) := by
  obtain ⟨r,htop,hstep⟩ := _root_.DerivativeChainContinuation.uniform_polynomial_tower n a
  have hc : r 0 0=_root_.DerivativeChainContinuation.complexCentroid a := by
    simpa only [htop] using (_root_.DerivativeChainPrefixLaws.uniform_row_centroid r n hstep n le_rfl).symm
  refine ⟨r,htop,hstep,hc,?_⟩
  intro h hh
  simpa only [hc,htop] using _root_.DerivativeChainPrefixLaws.uniform_tower_variance_contraction_div r n h hstep hh
