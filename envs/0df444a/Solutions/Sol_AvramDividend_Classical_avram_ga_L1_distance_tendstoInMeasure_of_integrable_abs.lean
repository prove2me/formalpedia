-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_L1_distance_tendstoInMeasure_of_integrable_abs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:01:16.550627+00:00
-- url     : https://prove2.me/submissions/247a5451-d642-4fff-84f0-b0afaf0503f3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hDiff : ∀ m, Integrable (fun ω => |Z ω - M m ω|) μ)
    (hLim : Tendsto (fun m => ∫ ω, |Z ω - M m ω| ∂μ)
      atTop (nhds (0 : ℝ))) :
    TendstoInMeasure μ M atTop Z := by
  have hLI (m : ℕ) :
      (∫⁻ ω, ENNReal.ofReal |Z ω - M m ω| ∂μ) =
      ENNReal.ofReal (∫ ω, |Z ω - M m ω| ∂μ) := by
    exact (ofReal_integral_eq_lintegral_ofReal (hDiff m)
      (ae_of_all μ fun ω => abs_nonneg _)).symm
  have hInt :
      Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal |Z ω - M m ω| ∂μ)
        atTop (nhds (0 : ℝ≥0∞)) := by
    simp_rw [hLI]
    change Tendsto (ENNReal.ofReal ∘ (fun m =>
      ∫ ω, |Z ω - M m ω| ∂μ)) atTop (nhds (0 : ℝ≥0∞))
    simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hLim
  refine tendstoInMeasure_iff_enorm.mpr ?_
  intro ε hε hεtop
  have hInvTop : ε⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hε.ne'
  have hUpper :
      Tendsto (fun m => ε⁻¹ * ∫⁻ ω, ENNReal.ofReal |Z ω - M m ω| ∂μ)
        atTop (nhds (0 : ℝ≥0∞)) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul (a := ε⁻¹) hInt (Or.inr hInvTop))
  have hBound (m : ℕ) :
      μ {ω | ε ≤ ‖M m ω - Z ω‖ₑ} ≤
        ε⁻¹ * ∫⁻ ω, ENNReal.ofReal |Z ω - M m ω| ∂μ := by
    have hMarkov :
        ε * μ {ω | ε ≤ ‖M m ω - Z ω‖ₑ} ≤
          ∫⁻ ω, ENNReal.ofReal |Z ω - M m ω| ∂μ := by
      simpa only [Real.enorm_eq_ofReal_abs, abs_sub_comm] using
        (mul_meas_ge_le_lintegral₀
          ((hDiff m).aemeasurable.ennreal_ofReal) ε)
    have hOne : ε⁻¹ * ε = 1 := by
      simpa [mul_comm] using ENNReal.mul_inv_cancel hε.ne' hεtop
    calc
      μ {ω | ε ≤ ‖M m ω - Z ω‖ₑ} =
          ε⁻¹ * (ε * μ {ω | ε ≤ ‖M m ω - Z ω‖ₑ}) := by
            rw [← mul_assoc, hOne, one_mul]
      _ ≤ ε⁻¹ * ∫⁻ ω, ENNReal.ofReal |Z ω - M m ω| ∂μ :=
        by gcongr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hUpper (fun _ => by positivity) hBound
