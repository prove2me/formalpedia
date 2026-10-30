-- Prove2me | solution 1 for DerivativeChainClusterAnchor.majority_atom_scalar_budget
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:54:47.695829+00:00
-- url     : https://prove2.me/submissions/480eb1f7-9def-4cba-8dcc-af64880851af

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
namespace DerivativeChainClusterAnchor

theorem cube_fraction_bound (N q k C : ℝ) (hN : 0 < N) (hq : 0 ≤ q) (hk : 0 < k)
    (hcube : C*q^3 ≤ N^2) (hscale : k^3 ≤ C*N) : k*q ≤ N := by
  by_contra h
  have hlt : N < k*q := lt_of_not_ge h
  have hx : 0 < k*q := hN.trans hlt
  have h1 := mul_lt_mul_of_pos_right hlt (sq_pos_of_pos hN)
  have h2 := mul_lt_mul_of_pos_right hlt (mul_pos hx hN)
  have h3 := mul_lt_mul_of_pos_right hlt (sq_pos_of_pos hx)
  have hu1 := mul_le_mul_of_nonneg_right hscale (pow_nonneg hq 3)
  have hu2 := mul_le_mul_of_nonneg_left hcube hN.le
  nlinarith





end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option maxHeartbeats 1500000
open DerivativeChainClusterAnchor

theorem solution (n r : ℕ) (hn : 8 ≤ n) (hr : 0 < r)
    (hcube : r^3 ≤ n^2) (R V δ : ℝ) (hR : 0 ≤ R) (hV0 : 0 ≤ V) (hδ0 : 0 ≤ δ)
    (hV : V ≤ 4*((r:ℝ)/(n:ℝ))*(1-(r:ℝ)/(n:ℝ))*R^2)
    (hδ : δ ≤ 2*((r:ℝ)/(n:ℝ))*R) :
    ((r:ℝ)-1)*Real.sqrt (V/((n:ℝ)-1))+
      Real.sqrt (((r:ℝ)-1)*V/((n:ℝ)-1)+δ^2) ≤ (2+Real.sqrt 2)*R := by
  have hnR : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hnm : (0:ℝ) < (n:ℝ)-1 := by linarith
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hfactor : 0 ≤ (r:ℝ)-1 := by linarith
  have hc : (r:ℝ)^3 ≤ (n:ℝ)^2 := by exact_mod_cast hcube
  have hfrac := _root_.DerivativeChainClusterAnchor.cube_fraction_bound (n:ℝ) (r:ℝ) 2 1 hn0 hr0 (by norm_num)
    (by simpa only [one_mul] using hc) (by nlinarith)
  have hθ : (r:ℝ)/(n:ℝ) ≤ 1/2 := (div_le_iff₀ hn0).mpr (by nlinarith)
  let K : ℝ := 4*(r:ℝ)*R^2/(n:ℝ)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hV' : V ≤ K*((n:ℝ)-(r:ℝ)) := hV.trans_eq (by dsimp [K]; field_simp <;> ring)
  have hVdiv : V/((n:ℝ)-1) ≤ K := by
    apply (div_le_iff₀ hnm).mpr
    exact hV'.trans (mul_le_mul_of_nonneg_left (by linarith : (n:ℝ)-(r:ℝ) ≤ (n:ℝ)-1) hK)
  let A := ((r:ℝ)-1)*Real.sqrt (V/((n:ℝ)-1))
  let C := Real.sqrt (((r:ℝ)-1)*V/((n:ℝ)-1)+δ^2)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hA2 : A^2 ≤ 4*R^2 := by
    dsimp [A]
    rw [mul_pow,Real.sq_sqrt (div_nonneg hV0 hnm.le)]
    calc
      _ ≤ (r:ℝ)^2*K := mul_le_mul (by nlinarith : ((r:ℝ)-1)^2 ≤ (r:ℝ)^2)
        hVdiv (div_nonneg hV0 hnm.le) (sq_nonneg _)
      _ = 4*(r:ℝ)^3*R^2/(n:ℝ)^2 := by dsimp [K]; ring
      _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos hn0)).mpr (by
        nlinarith only [mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ 4*R^2)])
  have hA : A ≤ 2*R := (sq_le_sq₀ hA0 (by positivity)).mp (by nlinarith)
  have hrow : ((r:ℝ)-1)*V/((n:ℝ)-1) ≤ 4*((r:ℝ)/(n:ℝ))^2*R^2 := by
    calc
      _ = ((r:ℝ)-1)*(V/((n:ℝ)-1)) := by ring
      _ ≤ ((r:ℝ)-1)*K := mul_le_mul_of_nonneg_left hVdiv hfactor
      _ ≤ (r:ℝ)*K := mul_le_mul_of_nonneg_right (by linarith : (r:ℝ)-1 ≤ r) hK
      _ = _ := by dsimp [K]; field_simp <;> ring
  have hδsq := (sq_le_sq₀ hδ0 (by positivity : 0 ≤ 2*((r:ℝ)/(n:ℝ))*R)).mpr hδ
  have hθsq := (sq_le_sq₀ (div_nonneg hr0 hn0.le) (by norm_num : (0:ℝ) ≤ 1/2)).mpr hθ
  have hC2 : C^2 ≤ 2*R^2 := by
    dsimp [C]
    rw [Real.sq_sqrt (by positivity : 0 ≤ ((r:ℝ)-1)*V/((n:ℝ)-1)+δ^2)]
    nlinarith [mul_le_mul_of_nonneg_right hθsq (sq_nonneg R)]
  have hC : C ≤ Real.sqrt 2*R := by
    apply (sq_le_sq₀ hC0 (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    exact hC2
  change A+C ≤ _
  nlinarith
