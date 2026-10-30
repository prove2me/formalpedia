-- Prove2me | solution 1 for DerivativeChainClusterAnchor.source_cluster_disk_moments
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:36:57.505185+00:00
-- url     : https://prove2.me/submissions/0411d5d9-8364-409d-bb12-e4392d5f0685

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Theorems.Thm_DerivativeChainClusterAnchor_cluster_source_centroid_variance
import Theorems.Thm_DerivativeChainPrefixLaws_source_uniform_variance_controlled_tower
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_centroid
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
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













end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
namespace DerivativeChainPrefixLaws
noncomputable section

theorem uniform_row_sum (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (h : ℕ) (hh : h ≤ n) :
    (∑ j : Fin (h+1), r h j)=(h+1:ℂ)*r 0 0 := by
  have hc := uniform_row_centroid r n hstep h hh
  have hn : (h+1:ℂ) ≠ 0 := by exact_mod_cast (show h+1 ≠ 0 by omega)
  have hs := (div_eq_iff hn).mp hc
  simpa only [mul_comm] using hs

theorem uniform_row_weighted_mean (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (h : ℕ) (hh : h ≤ n) :
    (∑ j : Fin (h+1), (((h+1:ℝ)⁻¹:ℝ):ℂ)*r h j)=r 0 0 := by
  rw [← Finset.mul_sum,uniform_row_sum r n hstep h hh]
  have hn : (h+1:ℂ) ≠ 0 := by exact_mod_cast (show h+1 ≠ 0 by omega)
  push_cast
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]





end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
namespace DerivativeChainClusterAnchor
noncomputable section

theorem source_mean_identity (n : ℕ) (a : Fin (n+1) → ℂ) :
    (∑ i, (((n+1:ℝ)⁻¹:ℝ):ℂ)*a i)=complexCentroid a := by
  obtain ⟨rows,htop,hstep,hcent,_⟩ := source_uniform_variance_controlled_tower n a
  simpa only [htop,hcent] using uniform_row_weighted_mean rows n hstep n le_rfl













end
end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
open DerivativeChainClusterAnchor




theorem solution (n r : ℕ) (a : Fin (n+1) → ℂ) (c o : ℂ)
    (O : Finset (Fin (n+1))) (hr : 0 < r) (hO : O.card ≤ r) (R ε : ℝ)
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (hsmall : ε ≤ R/(n+1:ℝ))
    (hsource : ∀ i, ‖a i-o‖ ≤ R) (hc : ‖c-o‖ ≤ R)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) :
    (∀ i, ‖a i-c‖ ≤ 2*R) ∧
      (∑ i, (n+1:ℝ)⁻¹*‖a i-_root_.DerivativeChainContinuation.complexCentroid a‖^2) ≤ 5*((r:ℝ)/(n+1:ℝ))*R^2 ∧
      ‖_root_.DerivativeChainContinuation.complexCentroid a-c‖ ≤ 3*((r:ℝ)/(n+1:ℝ))*R := by
  have hN : (0:ℝ) < n+1 := by positivity
  have hN1 : (1:ℝ) ≤ n+1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
  have hcross (i : Fin (n+1)) : ‖a i-c‖ ≤ 2*R := by
    have ht : ‖a i-c‖ ≤ ‖a i-o‖+‖o-c‖ := by simpa only [dist_eq_norm] using dist_triangle (a i) o c
    have hc' : ‖o-c‖ ≤ R := by simpa only [norm_sub_rev] using hc
    linarith [hsource i]
  have hεR : ε ≤ R := hsmall.trans
    ((div_le_iff₀ hN).mpr (by nlinarith [mul_nonneg hR (sub_nonneg.mpr hN1)]))
  have hεθ : ε ≤ ((r:ℝ)/(n+1:ℝ))*R := by
    calc
      _ ≤ R/(n+1:ℝ) := hsmall
      _ ≤ (r:ℝ)*R/(n+1:ℝ) := div_le_div_of_nonneg_right
        (by nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hR]) hN.le
      _ = _ := by ring
  have hεsq : ε^2 ≤ ((r:ℝ)/(n+1:ℝ))*R^2 := by
    calc
      _ ≤ ε*R := by nlinarith [mul_nonneg hε (sub_nonneg.mpr hεR)]
      _ ≤ (((r:ℝ)/(n+1:ℝ))*R)*R := mul_le_mul_of_nonneg_right hεθ hR
      _ = _ := by ring
  have hm := _root_.DerivativeChainClusterAnchor.cluster_source_centroid_variance a c (_root_.DerivativeChainContinuation.complexCentroid a) O (by omega) hO
    ε (2*R) hε (by positivity) hnear hcross
      (by simpa only [Nat.cast_add,Nat.cast_one] using _root_.DerivativeChainClusterAnchor.source_mean_identity n a)
  norm_num only [Nat.cast_add,Nat.cast_one] at hm
  refine ⟨hcross,?_,?_⟩
  · nlinarith [hm.1]
  · nlinarith [hm.2]
