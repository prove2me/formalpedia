-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.choice_of_exponent_constant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:17.959981+00:00
-- url     : https://prove2.me/submissions/aa3115a5-0779-4cf7-84ca-5096be15994e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NormOneEstimateOfHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
private theorem one_le_log_twelve : (1 : ℝ) ≤ Real.log 12 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : Formalism.HermitianLattices.ZeroFreeRegionGL2.ChoiceOfExponentConstant := by
  intro C C₀ c Cρ c₃ hC hC₀ hc hCρ hc₃
  set a : ℝ := Real.log (4 * Cρ) / c with ha
  set t : ℝ := max 1 (max (128 / c₃) (max C₀ (max C (a ^ 2)))) with ht
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht2 : 128 / c₃ ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  have ht3 : C₀ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have ht4 : C ≤ t :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have ht5 : a ^ 2 ≤ t :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  clear_value t
  refine ⟨2 * t + 14, by linarith, ?_⟩
  intro B hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hlB : 1 ≤ Real.log B := le_trans one_le_log_twelve (Real.log_le_log (by norm_num) hB)
  have hlB0 : 0 < Real.log B := by linarith
  have hlogX : Real.log (B ^ (2 * t + 14)) = (2 * t + 14) * Real.log B := Real.log_rpow hB0 _

  have key : ∀ s : ℝ, a ≤ s → Cρ * Real.exp (-c * s) ≤ 1 / 4 := by
    intro s hs
    have h1 : Real.log (4 * Cρ) ≤ c * s := by
      have := mul_le_mul_of_nonneg_left hs hc.le
      rw [ha] at this
      have e : c * (Real.log (4 * Cρ) / c) = Real.log (4 * Cρ) := by field_simp
      linarith
    have h2 : 4 * Cρ ≤ Real.exp (c * s) := by
      rw [← Real.log_le_iff_le_exp (by positivity)]; exact h1
    have h3 : Real.exp (-c * s) * Real.exp (c * s) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-c * s) := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left h2 h4.le]
  have hat : a ≤ Real.sqrt t := Real.le_sqrt_of_sq_le ht5
  have hst : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  refine ⟨?_, ?_⟩
  · unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.rho
    rw [hlogX]
    have e1 : -c * ((2 * t + 14) * Real.log B) / Real.log B = -c * (2 * t + 14) := by
      field_simp
    rw [e1, ← Real.sqrt_eq_rpow]
    have h1 := key (2 * t + 14) (by linarith)
    have h2 := key (Real.sqrt ((2 * t + 14) * Real.log B))
      (le_trans hat (Real.sqrt_le_sqrt (by nlinarith)))
    linarith
  · rw [hlogX]

    have hT : (0 : ℝ) < 2 * t + 14 := by linarith
    have e1 : (B ^ (2 * t + 14)) ^ (1 / 2 : ℝ) = B ^ (t + 7) := by
      rw [← Real.rpow_mul hB0.le]; congr 1; ring
    have e2 : B ^ (-6 : ℝ) * B ^ (2 * t + 14) = B ^ (t + 7) * (B ^ t * B) := by
      rw [← Real.rpow_add hB0]
      nth_rewrite 4 [← Real.rpow_one B]
      rw [← Real.rpow_add hB0, ← Real.rpow_add hB0]; congr 1; ring
    have hBC : B ^ C ≤ B ^ (t + 7) := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
    have hP : 0 < B ^ (t + 7) := Real.rpow_pos_of_pos hB0 _
    have hlogle : Real.log B ≤ B := by
      have := Real.log_le_sub_one_of_pos hB0; linarith

    have hBt : t ^ 2 / 2 ≤ B ^ t := by
      have h1 : Real.exp t ≤ B ^ t := by
        rw [Real.rpow_def_of_pos hB0]
        apply Real.exp_le_exp.2
        nlinarith
      have h2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ t by linarith)
      linarith
    have hct : 128 ≤ c₃ * t := by
      rw [div_le_iff₀ hc₃] at ht2; linarith
    have hmain : 4 * (2 * t + 14) ≤ c₃ * B ^ t := by
      have h1 : c₃ * (t ^ 2 / 2) ≤ c₃ * B ^ t := mul_le_mul_of_nonneg_left hBt hc₃.le
      have h2 : 64 * t ≤ c₃ * (t ^ 2 / 2) := by nlinarith
      linarith
    have hq : 4 * B ^ (t + 7) ≤ c₃ * B ^ (-6 : ℝ) * B ^ (2 * t + 14) / ((2 * t + 14) * Real.log B) := by
      rw [le_div_iff₀ (by positivity), mul_assoc c₃, e2]
      have h1 : (2 * t + 14) * Real.log B ≤ (2 * t + 14) * B := mul_le_mul_of_nonneg_left hlogle hT.le
      have h2 : 4 * ((2 * t + 14) * B) ≤ c₃ * B ^ t * B := by
        have := mul_le_mul_of_nonneg_right hmain hB0.le
        linarith
      calc 4 * B ^ (t + 7) * ((2 * t + 14) * Real.log B)
          = B ^ (t + 7) * (4 * ((2 * t + 14) * Real.log B)) := by ring
        _ ≤ B ^ (t + 7) * (c₃ * B ^ t * B) := mul_le_mul_of_nonneg_left (by linarith) hP.le
        _ = c₃ * (B ^ (t + 7) * (B ^ t * B)) := by ring
    rw [e1]
    linarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
