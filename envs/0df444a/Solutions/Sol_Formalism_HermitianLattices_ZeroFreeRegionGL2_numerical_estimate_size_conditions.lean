-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_estimate_size_conditions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:59.135804+00:00
-- url     : https://prove2.me/submissions/521cfea5-e8c9-4d8b-bf88-ae5ab48f73d6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_affine_log_le_rpow
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_pow_le_and_rho_le_of_log_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : ReciprocalWeightSizeConditions := by
  intro ε δ A integralAdeleSpan C_B C₀ c Cρ hε hδ hA hcT hCB hC₀ hc hCρ
  set K₀ : ℝ := |Real.log (200 * Cρ)| with hK₀
  have hsT : 0 < integralAdeleSpan ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hcT _
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_affine_log_le_rpow δ (C₀ * C_B) 0 integralAdeleSpan hδ hcT).and
      ((eventually_affine_log_le_rpow δ (K₀ * C_B) (A * C_B) (c * integralAdeleSpan) hδ (by positivity)).and
        ((eventually_affine_log_le_rpow (δ / 2) K₀ A (c * integralAdeleSpan ^ (1 / 2 : ℝ)) (by positivity) (by positivity)).and
          ((eventually_affine_log_le_rpow δ (7 * C_B) A (integralAdeleSpan / 3) hδ (by positivity)).and (eventually_ge_atTop (1 : ℝ))))))
  refine ⟨x₀, fun x hx B T m fk hB hlB hm hfk1 hfk2 hT hT0 => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  set L : ℝ := x ^ ε with hL
  set D : ℝ := x ^ δ with hD
  have hL1 : 1 ≤ L := Real.one_le_rpow e5 hε.le
  have hD0 : 0 < D := Real.rpow_pos_of_pos hx0 _
  have hlx : 0 ≤ Real.log x := Real.log_nonneg e5
  have hfk0 : 0 < fk := by linarith
  have hlB0 : 0 < Real.log B := Real.log_pos (by linarith)
  have hlfk : Real.log fk ≤ A * Real.log x := by
    have := Real.log_le_log hfk0 hfk2
    rwa [Real.log_rpow hx0] at this
  have hlfk0 : 0 ≤ Real.log fk := Real.log_nonneg hfk1

  have hT' : integralAdeleSpan * D * L ≤ Real.log T := by
    refine le_trans ?_ hT
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hcT.le) (by linarith)
  set K : ℝ := Real.log (200 * Cρ * fk) with hK
  have hKle : K ≤ K₀ + A * Real.log x := by
    rw [hK, Real.log_mul (by positivity) (by positivity)]
    have := le_abs_self (Real.log (200 * Cρ))
    linarith
  have hK₀0 : 0 ≤ K₀ := abs_nonneg _
  have hK2 : 0 ≤ K₀ + A * Real.log x := by positivity
  have k1 : C₀ * Real.log B ≤ Real.log T := by
    have t1 : C₀ * Real.log B ≤ C₀ * (C_B * L) := mul_le_mul_of_nonneg_left hlB hC₀.le
    have t2 : (C₀ * C_B + 0 * Real.log x) * L ≤ (integralAdeleSpan * D) * L := mul_le_mul_of_nonneg_right e1 (by linarith)
    nlinarith
  have hKe : Cρ * Real.exp (-K) ≤ 1 / fk / 200 := by
    rw [Real.exp_neg, hK, Real.exp_log (by positivity)]
    apply le_of_eq
    field_simp
  have k2 : K * Real.log B ≤ c * Real.log T := by
    have t1 : K * Real.log B ≤ (K₀ + A * Real.log x) * Real.log B := mul_le_mul_of_nonneg_right hKle hlB0.le
    have t2 : (K₀ + A * Real.log x) * Real.log B ≤ (K₀ + A * Real.log x) * (C_B * L) :=
      mul_le_mul_of_nonneg_left hlB hK2
    have t3 : (K₀ * C_B + A * C_B * Real.log x) * L ≤ (c * integralAdeleSpan * D) * L :=
      mul_le_mul_of_nonneg_right e2 (by linarith)
    have t4 : c * (integralAdeleSpan * D * L) ≤ c * Real.log T := mul_le_mul_of_nonneg_left hT' hc.le
    have t5 : (K₀ + A * Real.log x) * (C_B * L) = (K₀ * C_B + A * C_B * Real.log x) * L := by ring
    have t6 : c * (integralAdeleSpan * D * L) = (c * integralAdeleSpan * D) * L := by ring
    linarith
  have k3 : K ≤ c * Real.log T ^ (1 / 2 : ℝ) := by
    have t1 : integralAdeleSpan * D ≤ Real.log T := by
      refine le_trans ?_ hT'
      exact le_mul_of_one_le_right (by positivity) hL1
    have t2 : (integralAdeleSpan * D) ^ (1 / 2 : ℝ) ≤ Real.log T ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) t1 (by norm_num)
    have t3 : (integralAdeleSpan * D) ^ (1 / 2 : ℝ) = integralAdeleSpan ^ (1 / 2 : ℝ) * x ^ (δ / 2) := by
      rw [Real.mul_rpow hcT.le hD0.le, hD, ← Real.rpow_mul hx0.le]
      congr 2; ring
    have t4 : c * (integralAdeleSpan * D) ^ (1 / 2 : ℝ) ≤ c * Real.log T ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left t2 hc.le
    rw [t3] at t4
    linarith
  have k4 : 7 * Real.log B - Real.log (1 / fk) ≤ Real.log T / 3 := by
    rw [one_div, Real.log_inv]
    have t1 : (7 * C_B + A * Real.log x) * L ≤ (integralAdeleSpan / 3 * D) * L := mul_le_mul_of_nonneg_right e4 (by linarith)
    have t2 : A * Real.log x ≤ A * Real.log x * L := le_mul_of_one_le_right (by positivity) hL1
    nlinarith
  exact pow_le_and_rho_le_of_log_bounds C₀ c Cρ B T (1 / fk) K hCρ hB hT0 (by positivity) k1 hKe k2 k3 k4
end Formalism.HermitianLattices.ZeroFreeRegionGL2
