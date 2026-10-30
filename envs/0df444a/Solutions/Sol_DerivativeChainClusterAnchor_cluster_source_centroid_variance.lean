-- Prove2me | solution 1 for DerivativeChainClusterAnchor.cluster_source_centroid_variance
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:35:27.765956+00:00
-- url     : https://prove2.me/submissions/6ff22eb2-ebca-474e-8140-06df63c516be

import Mathlib
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
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
namespace DerivativeChainContinuation
open scoped BigOperators

theorem finite_norm_mean_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i, 0 ≤ w i) :
    ‖∑ i, (w i : ℂ)*z i‖ ≤ ∑ i, w i*‖z i‖ := by
  calc
    _ ≤ ∑ i, ‖(w i : ℂ)*z i‖ := norm_sum_le _ _
    _ = _ := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)]

theorem finite_distance_mean_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) (b x : ℂ)
    (hm : ∑ i, (w i : ℂ)*z i=b) :
    ‖x-b‖ ≤ ∑ i, w i*‖x-z i‖ := by
  have he : (∑ i, (w i:ℂ)*(x-z i))=x-b := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, hs, hm]
    simp
  simpa only [he] using finite_norm_mean_le w (fun i => x-z i) hw








end DerivativeChainContinuation



set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace DerivativeChainClusterAnchor
noncomputable section

theorem cluster_source_moment_bound {n r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hn : 0 < n) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) (hall : ∀ i, ‖a i-c‖ ≤ D) (k : ℕ) :
    (∑ i, (n:ℝ)⁻¹*‖a i-c‖^k) ≤ ε^k+(r:ℝ)/(n:ℝ)*D^k := by
  classical
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hpoint (i : Fin n) : ‖a i-c‖^k ≤ ε^k+(if i ∈ O then D^k else 0) := by
    split_ifs with hi
    · exact (pow_le_pow_left₀ (norm_nonneg _) (hall i) k).trans
        (le_add_of_nonneg_left (pow_nonneg hε k))
    · simpa only [add_zero] using pow_le_pow_left₀ (norm_nonneg _) (hnear i hi) k
  have hsum : (∑ i : Fin n, if i ∈ O then D^k else 0)=(O.card:ℝ)*D^k := by
    simp [Finset.sum_ite,Finset.filter_mem_eq_inter]
  have hfrac : (O.card:ℝ)/(n:ℝ) ≤ (r:ℝ)/(n:ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hO) hnR.le
  calc
    _ ≤ ∑ i, (n:ℝ)⁻¹*(ε^k+(if i ∈ O then D^k else 0)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (by positivity))
    _ = ε^k+(O.card:ℝ)/(n:ℝ)*D^k := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,hsum]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp <;> ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hfrac (pow_nonneg hD _))









end
end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open DerivativeChainClusterAnchor




theorem solution {n r : ℕ} (a : Fin n → ℂ) (c u : ℂ)
    (O : Finset (Fin n)) (hn : 0 < n) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) (hall : ∀ i, ‖a i-c‖ ≤ D)
    (hmean : (∑ i, (((n:ℝ)⁻¹:ℝ):ℂ)*a i)=u) :
    (∑ i, (n:ℝ)⁻¹*‖a i-u‖^2) ≤ ε^2+(r:ℝ)/(n:ℝ)*D^2 ∧
      ‖u-c‖ ≤ ε+(r:ℝ)/(n:ℝ)*D := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let w : Fin n → ℝ := fun _ => (n:ℝ)⁻¹
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; positivity
  have hs : ∑ i, w i=1 := by simp [w,hnR]
  have hvar := _root_.DerivativeChainContinuation.finite_weighted_variance w a u c hs hmean
  have hsecond := _root_.DerivativeChainClusterAnchor.cluster_source_moment_bound a c O hn hO ε D hε hD hnear hall 2
  have hfirst := _root_.DerivativeChainClusterAnchor.cluster_source_moment_bound a c O hn hO ε D hε hD hnear hall 1
  have hcent := _root_.DerivativeChainContinuation.finite_distance_mean_le w a hw hs u c hmean
  constructor
  · change (∑ i, w i*‖a i-u‖^2) ≤ _
    change (∑ i, w i*‖a i-c‖^2) ≤ _ at hsecond
    nlinarith [sq_nonneg ‖u-c‖]
  · simp only [pow_one] at hfirst
    have hcent' : ‖u-c‖ ≤ ∑ i, (n:ℝ)⁻¹*‖a i-c‖ := by
      simpa only [w,norm_sub_rev] using hcent
    exact hcent'.trans hfirst
