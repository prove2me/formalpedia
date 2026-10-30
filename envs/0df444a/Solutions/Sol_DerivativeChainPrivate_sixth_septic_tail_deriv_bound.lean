-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_septic_tail_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:07:42.785918+00:00
-- url     : https://prove2.me/submissions/a6a6e656-1d3d-4440-b056-cf0e76fad9db

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthSepticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_denominator_bound
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_tail_differentiableAt
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators



set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators















theorem norm_real_power_sum_le {n : ℕ} (c : Fin n → ℝ) (u : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hu : ‖u‖ ≤ R) :
    ‖∑ i : Fin n, (c i:ℂ)*u^i.val‖ ≤ ∑ i : Fin n, |c i| *R^i.val := by
  calc
    _ ≤ ∑ i : Fin n, ‖(c i:ℂ)*u^i.val‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      gcongr











end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators










theorem sixth_septic_residual_bound (u : ℂ) (hu : ‖u‖≤3/8) :
    ‖sixthSepticResidual u‖≤6600 := by
  apply (norm_real_power_sum_le sixthSepticResidualCoeffs u (3/8) (by norm_num) hu).trans
  norm_num [sixthSepticResidualCoeffs,Fin.sum_univ_succ]
end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainPrivate



theorem sixth_septic_tail_norm (w : ℂ) (hw : ‖w‖≤3/5) :
    ‖sixthSepticTail w‖≤11/1000000 := by
  have hu : ‖w^2‖≤3/8 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hk : 0<(3*Real.sqrt 15145/2720:ℝ) := by positivity
  have hku : (3*Real.sqrt 15145/2720:ℝ)≤7/50 := by
    have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤15145)
    have hp:=Real.sqrt_nonneg 15145
    nlinarith
  have ht:=sixth_septic_residual_bound (w^2) hu
  have hd:=(sixth_septic_denominator_bound (w^2) hu).2
  calc
    _=(3*Real.sqrt 15145/2720:ℝ)*‖w‖^39*‖sixthSepticResidual (w^2)‖*
        ‖(Complex.sqrt (sixthSepticRadicand (w^2))+sixthSepticPoly (w^2))⁻¹‖ := by
      simp only [sixthSepticTail,div_eq_mul_inv,norm_mul,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      norm_num [abs_of_nonneg (Real.sqrt_nonneg 15145)]
    _≤(7/50:ℝ)*(3/5)^39*6600*5 := by gcongr
    _≤11/1000000 := by norm_num




end DerivativeChainPrivate

theorem solution (w : ℂ) (hw : ‖w‖^2≤2/7) :
    ‖deriv sixthSepticTail w‖≤1/2000 := by
  have hw' : ‖w‖≤11/20 := by nlinarith [norm_nonneg w]
  have hball : ∀ u∈Metric.ball w (1/20:ℝ),‖u‖≤3/5 := by
    intro u hu
    have hd : ‖u-w‖<1/20 := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
    have hn:=norm_le_norm_sub_add u w
    linarith
  have hd : DifferentiableOn ℂ sixthSepticTail (Metric.ball w (1/20:ℝ)) := by
    intro u hu
    exact (sixth_septic_tail_differentiableAt u (hball u hu)).differentiableWithinAt
  have hm : Set.MapsTo sixthSepticTail (Metric.ball w (1/20:ℝ))
      (Metric.closedBall (sixthSepticTail w) (11/500000:ℝ)) := by
    intro u hu
    rw [Metric.mem_closedBall,dist_eq_norm]
    have h1:=sixth_septic_tail_norm u (hball u hu)
    have h2:=sixth_septic_tail_norm w (by linarith)
    have hn:=norm_sub_le (sixthSepticTail u) (sixthSepticTail w)
    linarith
  have hh:=Complex.norm_deriv_le_div_of_mapsTo_ball hd hm (by norm_num : (0:ℝ)<1/20)
  norm_num at hh
  linarith
