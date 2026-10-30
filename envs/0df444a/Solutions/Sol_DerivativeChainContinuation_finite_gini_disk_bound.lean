-- Prove2me | solution 1 for DerivativeChainContinuation.finite_gini_disk_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:42:29.335337+00:00
-- url     : https://prove2.me/submissions/5edc207a-5698-4346-832e-6916dc3f37e8

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



theorem finite_weighted_square_bound {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    (∑ i, w i*f i)^2 ≤ ∑ i, w i*(f i)^2 := by
  have h1 (i : ι) : Real.sqrt (w i)*(Real.sqrt (w i)*f i)=w i*f i := by
    rw [← mul_assoc,← pow_two,Real.sq_sqrt (hw i)]
  have h2 (i : ι) : (Real.sqrt (w i)*f i)^2=w i*(f i)^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i)*f i)
  simpa only [h1,h2,Real.sq_sqrt (hw _),hs,one_mul] using hh



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {ι : Type} [Fintype ι]
    (w : ι → ℝ) (z : ι → ℂ) (hw : ∀ i,0 ≤ w i) (hs : ∑ i,w i=1)
    (u a : ℂ) (D : ℝ) (hD : 0 ≤ D) (hm : ∑ i,(w i:ℂ)*z i=u)
    (hb : ∀ i,‖z i-a‖ ≤ D) :
    finiteGini w z ≤ Real.sqrt (2*(D^2-‖u-a‖^2)) := by
  let V := ∑ i,w i*‖z i-u‖^2
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hv := finite_weighted_variance w z u a hs hm
  have hDsq : (∑ i,w i*‖z i-a‖^2) ≤ D^2 := by
    calc
      _ ≤ ∑ i,w i*D^2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hD).mpr (hb i)) (hw i)
      _ = _ := by rw [← Finset.sum_mul,hs,one_mul]
  have hV : V ≤ D^2-‖u-a‖^2 := by dsimp [V]; linarith
  have hpair (i : ι) : (∑ j,w j*‖z i-z j‖^2)=‖z i-u‖^2+V := by
    simpa only [V,norm_sub_rev] using finite_weighted_variance w z u (z i) hs hm
  have henergy : (∑ i,∑ j,w i*w j*‖z i-z j‖^2)=2*V := by
    simp only [mul_assoc,← Finset.mul_sum,hpair,mul_add,Finset.sum_add_distrib,
      ← Finset.sum_mul,hs,one_mul]
    dsimp [V]
    ring
  have hweights : (∑ ij : ι × ι,w ij.1*w ij.2)=1 := by
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,hs,mul_one]
  have hsq := finite_weighted_square_bound (fun ij : ι × ι => w ij.1*w ij.2)
    (fun ij => ‖z ij.1-z ij.2‖) (fun ij => mul_nonneg (hw ij.1) (hw ij.2)) hweights
  simp only [Fintype.sum_prod_type] at hsq
  rw [henergy] at hsq
  change (finiteGini w z)^2 ≤ 2*V at hsq
  have hr : 0 ≤ 2*(D^2-‖u-a‖^2) := by linarith
  have hsqrt := Real.sq_sqrt hr
  have hg : 0 ≤ finiteGini w z := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hw i) (hw j)) (norm_nonneg _)
  nlinarith [Real.sqrt_nonneg (2*(D^2-‖u-a‖^2))]
