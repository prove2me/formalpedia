-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_tail_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:28:40.112092+00:00
-- url     : https://prove2.me/submissions/21aa3d9c-87fd-4a81-9822-16273a479397

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthOcticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_coefficient_bounds
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_denominator_bound
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_tail_differentiableAt
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
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators



















theorem sixth_octic_residual_bound (u : ℂ) (hu : ‖u‖≤3/10) :
    ‖sixthOcticResidual u‖≤848000 := by
  apply (norm_real_power_sum_le sixthOcticResidualCoeffs u (3/10) (by norm_num) hu).trans
  norm_num [sixthOcticResidualCoeffs,Fin.sum_univ_succ]


end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace DerivativeChainPrivate











theorem sixth_octic_pole_bound (u : ℂ) (hu : ‖u‖≤3/10) :
    1-(17/33:ℂ)*u≠0 ∧ ‖(1-(17/33:ℂ)*u)⁻¹‖≤6/5 := by
  have hn:=norm_sub_norm_le (1:ℂ) ((17/33:ℂ)*u)
  norm_num [norm_mul] at hn
  have hl : (5/6:ℝ)≤‖1-(17/33:ℂ)*u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi:=inv_anti₀ (by norm_num : (0:ℝ)<5/6) hl
  norm_num at hi
  exact hi
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



theorem sixth_octic_tail_norm (w : ℂ) (hw : ‖w‖≤27/50) : ‖sixthOcticTail w‖≤1/100000 := by
  have hu : ‖w^2‖≤3/10 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hk : 0<(3*Real.sqrt 429/1360:ℝ) := by positivity
  have hku : (3*Real.sqrt 429/1360:ℝ)≤23/500 := by
    have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤429)
    have hp:=Real.sqrt_nonneg 429
    nlinarith
  have ht:=sixth_octic_residual_bound (w^2) hu
  have hd:=(sixth_octic_denominator_bound (w^2) hu).2
  have hp:=(sixth_octic_pole_bound (w^2) hu).2
  have hL:=sixth_octic_coefficient_bounds.2.2.1
  have h1 : ‖(sixthOcticRationalTailCoeff:ℂ)*w^39/(1-(17/33:ℂ)*w^2)‖≤
      (4213:ℝ)*(27/50)^39*(6/5) := by
    calc
      _=|sixthOcticRationalTailCoeff| *‖w‖^39*‖(1-(17/33:ℂ)*w^2)⁻¹‖ := by
        simp [div_eq_mul_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      _≤_ := by gcongr
  have h2 : ‖((3*Real.sqrt 429/1360:ℝ):ℂ)*w^39*sixthOcticResidual (w^2)/
      (Complex.sqrt (sixthOcticRadicand (w^2))+sixthOcticPoly (w^2))/(1-(17/33:ℂ)*w^2)‖≤
      (23/500:ℝ)*(27/50)^39*848000*5*(6/5) := by
    calc
      _=(3*Real.sqrt 429/1360:ℝ)*‖w‖^39*‖sixthOcticResidual (w^2)‖*
          ‖(Complex.sqrt (sixthOcticRadicand (w^2))+sixthOcticPoly (w^2))⁻¹‖*
          ‖(1-(17/33:ℂ)*w^2)⁻¹‖ := by
        simp only [div_eq_mul_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
        norm_num [abs_of_nonneg (Real.sqrt_nonneg 429)]
      _≤_ := by gcongr
  unfold sixthOcticTail
  apply (norm_sub_le _ _).trans
  exact (add_le_add h1 h2).trans (by norm_num)




end DerivativeChainPrivate

theorem solution (w : ℂ) (hw : ‖w‖^2≤1/4) :
    ‖deriv sixthOcticTail w‖≤1/2000 := by
  have hw' : ‖w‖≤1/2 := by nlinarith [norm_nonneg w]
  have hball : ∀ u∈Metric.ball w (1/25:ℝ),‖u‖≤27/50 := by
    intro u hu
    have hd : ‖u-w‖<1/25 := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
    have hn:=norm_le_norm_sub_add u w
    linarith
  have hd : DifferentiableOn ℂ sixthOcticTail (Metric.ball w (1/25:ℝ)) := by
    intro u hu
    exact (sixth_octic_tail_differentiableAt u (hball u hu)).differentiableWithinAt
  have hm : Set.MapsTo sixthOcticTail (Metric.ball w (1/25:ℝ))
      (Metric.closedBall (sixthOcticTail w) (1/50000:ℝ)) := by
    intro u hu
    rw [Metric.mem_closedBall,dist_eq_norm]
    have h1:=sixth_octic_tail_norm u (hball u hu)
    have h2:=sixth_octic_tail_norm w (by linarith)
    have hn:=norm_sub_le (sixthOcticTail u) (sixthOcticTail w)
    linarith
  have hh:=Complex.norm_deriv_le_div_of_mapsTo_ball hd hm (by norm_num : (0:ℝ)<1/25)
  norm_num at hh
  exact hh
