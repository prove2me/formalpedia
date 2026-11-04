-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_centered_limit_of_L2_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:10:44.764315+00:00
-- url     : https://prove2.me/submissions/d06d6f02-9c18-45ee-aec4-4ea6a0c28be9

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

/-- An L² limit of integrable centred compensation variables has zero mean.
The L² convergence must be proved from a stochastic isometry separately. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (M : Ω → ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hMI : Integrable M P)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) = 0)
    (hConv2 : Tendsto
      (fun n => eLpNorm (fun ω => F n ω - M ω) 2 P)
      atTop (𝓝 0)) :
    (∫ ω, M ω ∂P) = 0 := by
  have hBound (n : ℕ) :
      (∫⁻ ω, ‖F n ω - M ω‖ₑ ∂P) ≤
      eLpNorm (fun ω => F n ω - M ω) 2 P := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((hFI n).sub hMI).aestronglyMeasurable
  have hConv1 : Tendsto
      (fun n => ∫⁻ ω, ‖F n ω - M ω‖ₑ ∂P)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) hConv2
    · intro n
      exact bot_le
    · intro n
      exact hBound n
  have hLimit := tendsto_integral_of_L1 M hMI.aestronglyMeasurable
    (Filter.Eventually.of_forall hFI) hConv1
  have hZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 (∫ ω, M ω ∂P)) := by
    simpa only [hMean] using hLimit
  exact (tendsto_nhds_unique tendsto_const_nhds hZero).symm
