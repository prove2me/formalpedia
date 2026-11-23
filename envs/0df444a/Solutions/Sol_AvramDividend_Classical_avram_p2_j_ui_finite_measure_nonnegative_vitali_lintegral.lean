-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_finite_measure_nonnegative_vitali_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:17:58.284005+00:00
-- url     : https://prove2.me/submissions/b81d038e-da9b-47d2-a35f-af7090ce8554

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_vitali_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_nonnegative_real_to_ennreal_mean_convergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped ENNReal

/-! Finite-measure nonnegative Vitali limits converge in genuine ENNReal means. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hUI : UniformIntegrable Y 1 μ)
    (hNonneg : ∀ n ω, 0 ≤ Y n ω)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧ (0 ≤ᵐ[μ] Z) ∧
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂μ)
        atTop (nhds (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)) := by
  obtain ⟨hZ, hMean⟩ :=
    avram_p2_j_ui_finite_measure_vitali_expectations μ Y Z hUI hae
  have hY : ∀ n, Integrable (Y n) μ :=
    fun n => memLp_one_iff_integrable.mp (hUI.memLp n)
  have hYn : ∀ n, 0 ≤ᵐ[μ] Y n :=
    fun n => Filter.Eventually.of_forall (hNonneg n)
  have hZn : 0 ≤ᵐ[μ] Z := by
    filter_upwards [hae] with ω hω
    exact ge_of_tendsto hω
      (Filter.Eventually.of_forall (fun n => hNonneg n ω))
  exact ⟨hZ, hZn,
    avram_p2_j_ui_nonnegative_real_to_ennreal_mean_convergence
      μ Y Z hY hZ hYn hZn hMean⟩
