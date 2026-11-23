-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_finite_measure_vitali_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:04:04.494268+00:00
-- url     : https://prove2.me/submissions/0879b0a4-c75e-4dc4-b758-b0466abff338

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter

/-! Genuine Bochner mean convergence under uniform integrability on finite measures. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hUI : UniformIntegrable Y 1 μ)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by
  have hZ : Integrable Z μ := hUI.integrable_of_ae_tendsto hae
  have hZLp : MemLp Z 1 μ := memLp_one_iff_integrable.mpr hZ
  have hmeas : ∀ n, AEStronglyMeasurable (Y n) μ :=
    fun n => hUI.aestronglyMeasurable n
  have hLp : Tendsto (fun n => eLpNorm (Y n - Z) 1 μ) atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
      hmeas hZLp hUI.unifIntegrable hae
  have hY : ∀ n, Integrable (Y n) μ :=
    fun n => memLp_one_iff_integrable.mp (hUI.memLp n)
  exact ⟨hZ, tendsto_integral_of_L1' Z hZ.aestronglyMeasurable
    (Filter.Eventually.of_forall hY) hLp⟩
