-- Prove2me | solution 1 for DerivativeChainClusterAnchor.eleven_thirds_scalar_budget
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:32:49.3488+00:00
-- url     : https://prove2.me/submissions/3c69a17d-e276-4c50-9156-2fb3eeda34ff

import Mathlib
import Theorems.Thm_DerivativeChainClusterAnchor_prefix_component_squares
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
open scoped BigOperators
open Finset Polynomial
namespace DerivativeChainClusterAnchor
noncomputable section













theorem nat_three_halves (r : ℕ) (hr : 0 < r) :
    (r:ℝ)^((3:ℝ)/2)=(r:ℝ)*Real.sqrt (r:ℝ) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  rw [show (3:ℝ)/2=1+1/2 by norm_num,Real.rpow_add hrR,Real.rpow_one,Real.sqrt_eq_rpow]



end
end DerivativeChainClusterAnchor



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



theorem tail_payment_square (n r : ℕ) (hr : 0 < r) (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 ≤ ε) :
    (16*(r:ℝ)^((3:ℝ)/2)*Real.sqrt (2*R*ε/(n:ℝ)))^2 =
      512*(r:ℝ)^3*R*ε/(n:ℝ) := by
  rw [nat_three_halves r hr]
  simp only [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*R*ε/(n:ℝ)),
    Real.sq_sqrt (Nat.cast_nonneg r)]
  ring

end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option maxHeartbeats 1500000
open DerivativeChainClusterAnchor

theorem solution (n r : ℕ) (hn : 16 ≤ n) (hr : 0 < r)
    (hcube : 16*r^3 ≤ n^2) (R V δ ε : ℝ) (hR : 0 ≤ R) (hV0 : 0 ≤ V)
    (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hV : V ≤ 5*((r:ℝ)/(n:ℝ))*R^2)
    (hδ : δ ≤ 3*((r:ℝ)/(n:ℝ))*R) (hε : ε ≤ R/(16*(n:ℝ))) :
    (2*(r:ℝ)-1)*Real.sqrt (V/((n:ℝ)-1))+
      Real.sqrt ((2*(r:ℝ)-1)*V/((n:ℝ)-1)+δ^2)+4*(n:ℝ)*ε+
      16*(r:ℝ)^((3:ℝ)/2)*Real.sqrt (2*R*ε/(n:ℝ)) ≤ (11/3:ℝ)*R := by
  have hnR : (16:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hnm : (0:ℝ) < (n:ℝ)-1 := by linarith
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hh0 : (0:ℝ) ≤ 2*(r:ℝ)-1 := by linarith
  have hc : (16:ℝ)*(r:ℝ)^3 ≤ (n:ℝ)^2 := by exact_mod_cast hcube
  have hfrac := _root_.DerivativeChainClusterAnchor.cube_fraction_bound (n:ℝ) (r:ℝ) 6 16 hn0 hr0 (by norm_num) hc (by nlinarith)
  have hθ : (r:ℝ)/(n:ℝ) ≤ 1/6 := (div_le_iff₀ hn0).mpr (by nlinarith)
  let A := (2*(r:ℝ)-1)*Real.sqrt (V/((n:ℝ)-1))
  let C := Real.sqrt ((2*(r:ℝ)-1)*V/((n:ℝ)-1)+δ^2)
  let T := 16*(r:ℝ)^((3:ℝ)/2)*Real.sqrt (2*R*ε/(n:ℝ))
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hp := _root_.DerivativeChainClusterAnchor.prefix_component_squares (n:ℝ) (r:ℝ) R V δ (by linarith) hr1
    (by linarith) hR hV0 hδ0 hV hδ
  change A^2 ≤ _ ∧ C^2 ≤ _ at hp
  have hscalar : 20*(r:ℝ)^3 ≤ (4/3:ℝ)*(n:ℝ)*((n:ℝ)-1) := by
    nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hnR)]
  have hA2 : A^2 ≤ (4/3:ℝ)*R^2 := by
    apply hp.1.trans
    apply (div_le_iff₀ (mul_pos hn0 hnm)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hscalar (sq_nonneg R)]
  have hA : A ≤ (7/6:ℝ)*R := (sq_le_sq₀ hA0 (by positivity)).mp (by nlinarith [sq_nonneg R])
  have hθsq := (sq_le_sq₀ (div_nonneg hr0 hn0.le) (by norm_num : (0:ℝ) ≤ 1/6)).mpr hθ
  have hC : C ≤ (3/4:ℝ)*R := by
    apply (sq_le_sq₀ hC0 (by positivity)).mp
    nlinarith [mul_le_mul_of_nonneg_right hθsq (sq_nonneg R),hp.2]
  have hεmul := (le_div_iff₀ (by positivity : (0:ℝ) < 16*(n:ℝ))).mp hε
  have hεn : ε*(n:ℝ) ≤ R/16 := by nlinarith only [hεmul]
  have hTidentity : T^2=512*(r:ℝ)^3*R*ε/(n:ℝ) := _root_.DerivativeChainClusterAnchor.tail_payment_square n r hr R ε hR hε0
  have hTc : T^2*(n:ℝ)^2 ≤ 2*R^2*(n:ℝ)^2 := by
    have he : T^2*(n:ℝ)^2=512*(r:ℝ)^3*R*ε*(n:ℝ) := by
      rw [hTidentity]
      field_simp <;> ring
    rw [he]
    have ht := mul_le_mul_of_nonneg_left hεn (by positivity : (0:ℝ) ≤ 512*(r:ℝ)^3*R)
    have hcr := mul_le_mul_of_nonneg_right hc (sq_nonneg R)
    nlinarith only [ht,hcr]
  have hT2 : T^2 ≤ 2*R^2 := (mul_le_mul_iff_left₀ (sq_pos_of_pos hn0)).mp hTc
  have hT : T ≤ (3/2:ℝ)*R := (sq_le_sq₀ hT0 (by positivity)).mp (by nlinarith [sq_nonneg R])
  change A+C+4*(n:ℝ)*ε+T ≤ _
  nlinarith
