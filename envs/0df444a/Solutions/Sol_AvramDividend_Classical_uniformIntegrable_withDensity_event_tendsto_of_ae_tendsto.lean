-- Prove2me | solution 1 for AvramDividend.Classical.uniformIntegrable_withDensity_event_tendsto_of_ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:48:38.804127+00:00
-- url     : https://prove2.me/submissions/c1e83cfe-de19-4c4c-8263-84f726acf111

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hUI : UniformIntegrable f 1 μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hpos : ∀ n ω, 0 ≤ f n ω) (hgpos : ∀ ω, 0 ≤ g ω)
    (A : Set Ω) (hA : MeasurableSet A) :
    Tendsto (fun n => (μ.withDensity
      (fun ω => ENNReal.ofReal (f n ω))) A)
      atTop (𝓝 ((μ.withDensity
        (fun ω => ENNReal.ofReal (g ω))) A)) := by
  have hg : Integrable g μ := hUI.integrable_of_ae_tendsto hlim
  have hLp : Tendsto (fun n => eLpNorm (f n - g) 1 μ)
      atTop (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_Lp_finite_of_tendsto_ae
      (by norm_num) (by norm_num)
      (fun n => hUI.1 n)
      (memLp_one_iff_integrable.mpr hg)
      hUI.2.1 hlim
  have hv : Tendsto (fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ∂μ)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using hLp
  have hfn (n : ℕ) : Integrable (f n) μ :=
    memLp_one_iff_integrable.mp (hUI.memLp n)
  have hi : Tendsto (fun n => ∫ ω in A, f n ω ∂μ)
      atTop (𝓝 (∫ ω in A, g ω ∂μ)) :=
    tendsto_setIntegral_of_L1 g hg.aestronglyMeasurable
      (Eventually.of_forall hfn) hv A
  have hEvent (n : ℕ) :
      (μ.withDensity (fun ω => ENNReal.ofReal (f n ω))) A =
        ENNReal.ofReal (∫ ω in A, f n ω ∂μ) := by
    rw [withDensity_apply _ hA]
    exact (ofReal_integral_eq_lintegral_ofReal
      (hfn n).integrableOn
      (Eventually.of_forall fun ω => hpos n ω)).symm
  have hEventG :
      (μ.withDensity (fun ω => ENNReal.ofReal (g ω))) A =
        ENNReal.ofReal (∫ ω in A, g ω ∂μ) := by
    rw [withDensity_apply _ hA]
    exact (ofReal_integral_eq_lintegral_ofReal
      hg.integrableOn
      (Eventually.of_forall fun ω => hgpos ω)).symm
  rw [hEventG]
  simpa only [hEvent] using ENNReal.tendsto_ofReal hi
