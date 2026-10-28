-- Prove2me | solution 1 for AvramDividend.Classical.uniformIntegrable_integral_mass_one_of_ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:26:41.54499+00:00
-- url     : https://prove2.me/submissions/26e2e038-29ed-4619-9ce7-fde22dae0c84

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hUI : UniformIntegrable f 1 μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hmass : ∀ n, (∫ ω, f n ω ∂μ) = (1 : ℝ)) :
    (∫ ω, g ω ∂μ) = (1 : ℝ) := by
  have hg : Integrable g μ :=
    hUI.integrable_of_ae_tendsto hlim
  have hgLp : MemLp g 1 μ :=
    memLp_one_iff_integrable.mpr hg
  have hv : Tendsto (fun n => eLpNorm (f n - g) 1 μ)
      atTop (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_Lp_finite_of_tendsto_ae
      (by norm_num) (by norm_num)
      (fun n => hUI.1 n) hgLp hUI.2.1 hlim
  have hv' : Tendsto
      (fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ∂μ)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using hv
  have hfin : ∀ n, Integrable (f n) μ := by
    intro n
    exact memLp_one_iff_integrable.mp (hUI.memLp n)
  have hi : Tendsto (fun n => ∫ ω, f n ω ∂μ)
      atTop (𝓝 (∫ ω, g ω ∂μ)) :=
    tendsto_integral_of_L1 g hg.aestronglyMeasurable
      (Eventually.of_forall hfin) hv'
  have hone : Tendsto (fun n => ∫ ω, f n ω ∂μ)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [hmass] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  exact tendsto_nhds_unique hi hone
