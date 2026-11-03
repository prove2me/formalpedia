-- Prove2me | solution 1 for AvramDividend.Classical.bv_levy_transition_right_generator_of_global_C1_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:47:15.25519+00:00
-- url     : https://prove2.me/submissions/0428b0d6-7eb8-4a1d-8e41-5ee979fa128c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_right_slope
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integral
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_integrable_signed_negative_jump_tail_DCT
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_endpoint_poly_levy_integrable
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_signed_payoff_BV_Levy_L1_error_transfer
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_poly_residual_primitive_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_original_C1_source_drift_expectation_right_slope
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_avram_chat07a_original_bv_zero_at_one_poly_residual_slope
import Theorems.Thm_avram_chat07a_joint_source_and_levy_poly_approx
import Theorems.Thm_avram_chat07a_residual_and_poly_integrability
import Theorems.Thm_avram_chat07a_residual_limit_assembly
import Theorems.Thm_avram_chat07a_final_drift_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ * ((∫ ω, w (x + X.X (Real.toNNReal h) ω) ∂P) - w x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (X.generator w x)) := by
  obtain ⟨hF, hPoly⟩ :=
    avram_chat07a_residual_and_poly_integrability X hX hBV w hwC1 L hL hLip x
  have hSlope (Q : Polynomial ℝ) (hQ : Polynomial.eval 1 Q = 0) :=
    avram_chat07a_original_bv_zero_at_one_poly_residual_slope X hBV Q hQ
  have hJoint (η : ℝ) (hη : 0 < η) :=
    avram_chat07a_joint_source_and_levy_poly_approx
      X hX hBV w hwC1 L hL hLip x hgen η hη
  have hRes :=
    avram_chat07a_residual_limit_assembly X w L x hF hPoly hSlope hJoint
  exact avram_chat07a_final_drift_bridge
    X hX hBV w hwC1 L hL hLip x hgen hRes