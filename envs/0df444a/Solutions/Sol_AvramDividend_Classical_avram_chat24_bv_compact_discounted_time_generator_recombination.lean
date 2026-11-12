-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_bv_compact_discounted_time_generator_recombination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:35:25.406984+00:00
-- url     : https://prove2.me/submissions/f80eac43-174a-4020-b2a0-7de5333ff0dc

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_compact_finite_measure_generator_recombination
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_negative_jump_generator_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_chat24_positive_shift_compact_kernel_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hs : ContDiffOn ℝ 1 w (Ioi 0)) (q a b : ℝ)
    (hq : 0 ≤ q) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hgen : ∀ y ∈ Icc a b, X.GeneratorIntegrable w y)
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (Y : ℝ≥0 → ℝ) (hYm : Measurable Y) (τ : ℝ≥0) :
    (∫ t, if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Y t) - q * w (Y t)) else 0 ∂μ) =
    -(∫ t, ∫ z in Iio (0 : ℝ), if t ≤ τ ∧ Y t ∈ Icc a b ∧ z < 0 then
      Real.exp (-(q * (t : ℝ))) * (w (Y t + z) - w (Y t)) else 0 ∂X.ν ∂μ) +
    (∫ t, if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * (X.generator w (Y t) - q * w (Y t)) else 0 ∂μ) := by
  classical
  obtain ⟨L, R, hL, hR, hLip, hW⟩ :=
    avram_chat24_positive_shift_compact_kernel_bounds w hw_cont hw_neg hs a b ha hab
  have hdc : ContinuousOn (deriv w) (Ioi 0) :=
    hs.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hdc.mono (show Icc a b ⊆ Ioi 0 from fun y hy => ha.trans_le hy.1))
  have hDeriv (y : ℝ) (hy : y ∈ Icc a b) : |deriv w y| ≤ max A 0 := by
    simpa only [Real.norm_eq_abs] using (hA y hy).trans (le_max_left A 0)
  have hwm := avram_p3_e_compensator_original_ruin_extension_value_measurable w hw_cont hw_neg
  let E : Set ℝ≥0 := Iic τ ∩ Y ⁻¹' Icc a b
  have hEm : MeasurableSet E := measurableSet_Iic.inter (measurableSet_Icc.preimage hYm)
  let e : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  have hem : Measurable e := by dsimp [e]; fun_prop
  have he (t : ℝ≥0) : |e t| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq t.coe_nonneg))
  have hp := avram_chat24_bv_compact_finite_measure_generator_recombination
    X hBV w hwm q a b L R (max A 0) ha ha2 hab hL hR (le_max_right _ _)
    hLip hW hDeriv hgen μ Y e hYm hem he E hEm (fun t ht => ht.2)
  have hkernel (t : ℝ≥0) :
      (∫ z in Iio (0 : ℝ), if t ≤ τ ∧ Y t ∈ Icc a b ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) * (w (Y t + z) - w (Y t)) else 0 ∂X.ν) =
      if t ∈ E then e t * (∫ z in Iio (0 : ℝ), w (Y t + z) - w (Y t) ∂X.ν) else 0 := by
    calc
      _ = ∫ z in Iio (0 : ℝ), if t ∈ E then
          e t * (w (Y t + z) - w (Y t)) else 0 ∂X.ν := by
        apply setIntegral_congr_fun measurableSet_Iio
        intro z hz
        have hz0 : z < (0 : ℝ) := hz
        have hcond : (t ≤ τ ∧ Y t ∈ Icc a b ∧ z < 0) ↔ t ∈ E :=
          ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hz0⟩⟩
        simp only [hcond, e]
      _ = _ := by
        by_cases ht : t ∈ E <;> simp [ht, integral_const_mul]
  simp_rw [hkernel]
  simpa only [E, e, mem_inter_iff, mem_Iic, mem_preimage] using hp
