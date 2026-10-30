-- Prove2me | solution 1 for DerivativeChainClusterAnchor.prefix_component_squares
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:31:38.148713+00:00
-- url     : https://prove2.me/submissions/c26f10b1-a54b-4058-8c4b-a0e18cf7c1d8

import Mathlib
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
set_option maxHeartbeats 1500000
open DerivativeChainClusterAnchor



theorem solution (N q R V δ : ℝ) (hN : 1 < N) (hq : 1 ≤ q)
    (hcut : 2*q ≤ N) (hR : 0 ≤ R) (hV0 : 0 ≤ V) (hδ0 : 0 ≤ δ)
    (hV : V ≤ 5*(q/N)*R^2) (hδ : δ ≤ 3*(q/N)*R) :
    ((2*q-1)*Real.sqrt (V/(N-1)))^2 ≤ 20*q^3*R^2/(N*(N-1)) ∧
      (Real.sqrt ((2*q-1)*V/(N-1)+δ^2))^2 ≤ 19*(q/N)^2*R^2 := by
  have hN0 : 0 < N := by linarith
  have hNm : 0 < N-1 := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hh : 0 ≤ 2*q-1 := by linarith
  have hV' : V ≤ 5*q*R^2/N := hV.trans_eq (by ring)
  have hVN : V*N ≤ 5*q*R^2 := (le_div_iff₀ hN0).mp hV'
  have hcoef : (2*q-1)^2 ≤ 4*q^2 := by nlinarith
  have hnum1 := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hN0.le hV0)
  have hnum2 := mul_le_mul_of_nonneg_left hVN (by positivity : 0 ≤ 4*q^2)
  have hnum : ((2*q-1)^2*V)*N ≤ 20*q^3*R^2 := by nlinarith only [hnum1,hnum2]
  constructor
  · rw [mul_pow,Real.sq_sqrt (div_nonneg hV0 hNm.le),← mul_div_assoc]
    apply (div_le_div_iff₀ hNm (mul_pos hN0 hNm)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hnum hNm.le]
  · have hγ : (2*q-1)/(N-1) ≤ 2*q/N := by
      apply (div_le_div_iff₀ hNm hN0).mpr
      nlinarith
    have hγV := mul_le_mul_of_nonneg_right hγ hV0
    have hVV := mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 2*q/N)
    have hδsq := (sq_le_sq₀ hδ0 (by positivity : 0 ≤ 3*(q/N)*R)).mpr hδ
    rw [Real.sq_sqrt (by positivity : 0 ≤ (2*q-1)*V/(N-1)+δ^2)]
    calc
      _ = ((2*q-1)/(N-1))*V+δ^2 := by ring
      _ ≤ (2*q/N)*V+(3*(q/N)*R)^2 := add_le_add hγV hδsq
      _ ≤ (2*q/N)*(5*(q/N)*R^2)+(3*(q/N)*R)^2 := add_le_add hVV le_rfl
      _ = _ := by ring
