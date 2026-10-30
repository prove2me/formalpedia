-- Prove2me | solution 1 for DerivativeChainClusterAnchor.majority_atom_source_variance
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:56:36.691414+00:00
-- url     : https://prove2.me/submissions/7950ac52-f04d-45c2-ab7b-8f1fd56a8f3b

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
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace DerivativeChainClusterAnchor
noncomputable section







theorem sharp_two_level_source_moment {n r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hn : 0 < n) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 ≤ ε) (hεD : ε ≤ D)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) (hall : ∀ i, ‖a i-c‖ ≤ D) (k : ℕ) :
    (∑ i, (n:ℝ)⁻¹*‖a i-c‖^k) ≤ ε^k+(r:ℝ)/(n:ℝ)*(D^k-ε^k) := by
  classical
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hdiff : 0 ≤ D^k-ε^k := sub_nonneg.mpr (pow_le_pow_left₀ hε hεD k)
  have hpoint (i : Fin n) : ‖a i-c‖^k ≤ ε^k+(if i ∈ O then D^k-ε^k else 0) := by
    split_ifs with hi
    · simpa only [add_sub_cancel] using pow_le_pow_left₀ (norm_nonneg _) (hall i) k
    · simpa only [add_zero] using pow_le_pow_left₀ (norm_nonneg _) (hnear i hi) k
  have hsum : (∑ i : Fin n, if i ∈ O then D^k-ε^k else 0)=(O.card:ℝ)*(D^k-ε^k) := by simp [mul_sub]
  have hfrac : (O.card:ℝ)/(n:ℝ) ≤ (r:ℝ)/(n:ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hO) hnR.le
  calc
    _ ≤ ∑ i, (n:ℝ)⁻¹*(ε^k+(if i ∈ O then D^k-ε^k else 0)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (by positivity))
    _ = ε^k+(O.card:ℝ)/(n:ℝ)*(D^k-ε^k) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,hsum]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp <;> ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hfrac hdiff)



end
end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open DerivativeChainClusterAnchor










theorem solution {n r : ℕ} (a : Fin n → ℂ) (c o u : ℂ)
    (O : Finset (Fin n)) (hn : 0 < n) (hO : O.card ≤ r) (hhalf : 2*r ≤ n)
    (R : ℝ) (hR : 0 ≤ R) (hc : ‖c-o‖ ≤ R) (hall : ∀ i, ‖a i-o‖ ≤ R)
    (hnear : ∀ i, i ∉ O → a i=c)
    (hmean : (∑ i, (((n:ℝ)⁻¹:ℝ):ℂ)*a i)=u) :
    (∑ i, (n:ℝ)⁻¹*‖a i-u‖^2) ≤ 4*((r:ℝ)/(n:ℝ))*(1-(r:ℝ)/(n:ℝ))*R^2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let α : ℝ := (r:ℝ)/(n:ℝ)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hαhalf : α ≤ 1/2 := by
    dsimp [α]
    apply (div_le_iff₀ hnR).mpr
    have hh : (2:ℝ)*(r:ℝ) ≤ n := by exact_mod_cast hhalf
    nlinarith
  have hweight : 0 ≤ 1-2*α := by linarith
  let v : ℂ := ((1-2*α:ℝ):ℂ)*c+((2*α:ℝ):ℂ)*o
  have hcEq : c-v=((2*α:ℝ):ℂ)*(c-o) := by dsimp [v]; push_cast; ring
  have hcv : ‖c-v‖ ≤ 2*α*R := by
    rw [hcEq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 2*α)]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hav (i : Fin n) : ‖a i-v‖ ≤ 2*(1-α)*R := by
    calc
      _ = ‖(a i-o)+((1-2*α:ℝ):ℂ)*(o-c)‖ := by congr 1; dsimp [v]; push_cast; ring
      _ ≤ ‖a i-o‖+‖((1-2*α:ℝ):ℂ)*(o-c)‖ := norm_add_le _ _
      _ = ‖a i-o‖+(1-2*α)*‖c-o‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hweight,norm_sub_rev o c]
      _ ≤ R+(1-2*α)*R := add_le_add (hall i) (mul_le_mul_of_nonneg_left hc hweight)
      _ = _ := by ring
  have horder : 2*α*R ≤ 2*(1-α)*R := by nlinarith [mul_nonneg hweight hR]
  have hb := _root_.DerivativeChainClusterAnchor.sharp_two_level_source_moment a v O hn hO (2*α*R) (2*(1-α)*R)
    (by positivity) horder (fun i hi => by rw [hnear i hi]; exact hcv) hav 2
  have hb' : (∑ i, (n:ℝ)⁻¹*‖a i-v‖^2) ≤ 4*α*(1-α)*R^2 :=
    hb.trans_eq (by dsimp [α]; ring)
  let w : Fin n → ℝ := fun _ => (n:ℝ)⁻¹
  have hs : ∑ i, w i=1 := by simp [w,hnR.ne']
  have hv := _root_.DerivativeChainContinuation.finite_weighted_variance w a u v hs hmean
  change (∑ i, w i*‖a i-u‖^2) ≤ _
  change (∑ i, w i*‖a i-v‖^2) ≤ _ at hb'
  change (∑ i, w i*‖a i-u‖^2) ≤ 4*α*(1-α)*R^2
  nlinarith [sq_nonneg ‖u-v‖]
