-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a103_original_gaussian_true_random_crossing_source_increment_expected_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:45:30.722591+00:00
-- url     : https://prove2.me/submissions/8a0b3663-71fb-46e5-8943-fe4e59e33734

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Original Gaussian true random physical crossing source displacement converges in expected L1 under an integrable supremum envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => |X.X (t m ω) ω - X.X (s m ω) ω|) P)
    (bound : Ω → ℝ) (hBI : Integrable bound P)
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      |X.X (t m ω) ω - X.X (s m ω) ω| ≤ bound ω) :
    Tendsto (fun m => ∫ ω,
      |X.X (t m ω) ω - X.X (s m ω) ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hAE := avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
    X hν T s t hRange hGap
  have hAbs : ∀ᵐ ω ∂P, Tendsto
      (fun m => |X.X (t m ω) ω - X.X (s m ω) ω|)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hAE] with ω h
    simpa only [abs_zero] using h.abs
  have hNorm (m : ℕ) : ∀ᵐ ω ∂P,
      ‖|X.X (t m ω) ω - X.X (s m ω) ω|‖ ≤ bound ω := by
    filter_upwards [hDom m] with ω hd
    simpa only [Real.norm_eq_abs, abs_abs] using hd
  have h := tendsto_integral_of_dominated_convergence
    bound hMeas hBI hNorm hAbs
  simpa only [integral_zero] using h
