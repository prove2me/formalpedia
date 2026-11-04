-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_second_moment_to_l2_norm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:19:36.618045+00:00
-- url     : https://prove2.me/submissions/d99a1c34-55d2-490a-a018-5cba52f1bc4c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-! The genuine real second-moment integral controls the L² seminorm. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (B : ℝ≥0)
    (hm : AEStronglyMeasurable Y P)
    (hInt : Integrable (fun ω => ‖Y ω‖ ^ 2) P)
    (hBound : (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ (B : ℝ) ^ 2) :
    eLpNorm Y 2 P ≤ (B : ENNReal) := by
  have h2 : MemLp Y 2 P :=
    (memLp_two_iff_integrable_sq_norm hm).mpr hInt
  have hb0 : (0 : ℝ) ≤ (B : ℝ) := B.property
  have hroot : Real.sqrt (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ (B : ℝ) := by
    calc
      Real.sqrt (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤
          Real.sqrt ((B : ℝ) ^ 2) := Real.sqrt_le_sqrt hBound
      _ = (B : ℝ) := by
        simpa [abs_of_nonneg hb0] using (Real.sqrt_sq_eq_abs (B : ℝ))
  have hENN := ENNReal.ofReal_le_ofReal hroot
  have hpowIntegral :
      (∫ ω, ‖Y ω‖ ^ (2 : ℝ) ∂P) =
      (∫ ω, ‖Y ω‖ ^ 2 ∂P) := by
    apply integral_congr_ae
    filter_upwards [] with ω
    norm_num [Real.rpow_natCast]
  have hsqrt :
      (∫ ω, ‖Y ω‖ ^ (2 : ℝ) ∂P) ^ ((2 : ℝ)⁻¹) =
        Real.sqrt (∫ ω, ‖Y ω‖ ^ 2 ∂P) := by
    rw [hpowIntegral]
    simpa only [one_div] using
      (Real.sqrt_eq_rpow (∫ ω, ‖Y ω‖ ^ 2 ∂P)).symm
  rw [h2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simpa only [ENNReal.toReal_ofNat, hsqrt,
    ENNReal.ofReal_coe_nnreal] using hENN
