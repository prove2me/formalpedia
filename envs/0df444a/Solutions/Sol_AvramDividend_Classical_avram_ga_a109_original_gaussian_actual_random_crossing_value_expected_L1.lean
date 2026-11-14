-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a109_original_gaussian_actual_random_crossing_value_expected_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:52:43.398654+00:00
-- url     : https://prove2.me/submissions/4a0b1b97-0afc-4028-a9e7-b0a1440f9577

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a28_compact_modulus_last_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section
/-- The genuinely randomly stopped Gaussian crossing source value displacement is expected-L1 small under a positive compact band and an integrable envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m, s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (α β : ℝ) (hα : 0 < α) (y : ℕ → Ω → ℝ)
    (hBase : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, α ≤ y m ω ∧ y m ω ≤ β)
    (w : ℝ → ℝ)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, u ∈ Icc (α / 2) (β + α / 2) →
        v ∈ Icc (α / 2) (β + α / 2) →
        |v - u| < δ → |w v - w u| < ε)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)|) P)
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)| ≤ B ω) :
    Tendsto (fun m => ∫ ω,
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)| ∂P) atTop (𝓝 (0 : ℝ)) := by
  have hXae := avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero X hν T s t hRange hGap
  have hWae : ∀ᵐ ω ∂P, Tendsto (fun m =>
      w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hXae, hBase] with ω hInc hY
    have hPos : 0 < α / 2 := by positivity
    have hSmall : ∀ᶠ m in atTop,
        |X.X (t m ω) ω - X.X (s m ω) ω| < α / 2 := by
      obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.1 hInc) (α / 2) hPos
      filter_upwards [Filter.eventually_ge_atTop N] with m hm
      simpa only [Real.dist_eq, sub_zero] using hN m hm
    have hPair : ∀ᶠ m in atTop,
        y m ω ∈ Icc (α / 2) (β + α / 2) ∧
          y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ∈
            Icc (α / 2) (β + α / 2) := by
      filter_upwards [hY, hSmall] with m hB hS
      obtain ⟨hLo,hHi⟩ := hB; obtain ⟨hDL,hDU⟩ := abs_lt.mp hS
      exact ⟨⟨by linarith, by linarith⟩,
        ⟨by linarith, by linarith⟩⟩
    have hLo : ∀ᶠ m in atTop, y m ω ∈
        Icc (α / 2) (β + α / 2) :=
      hPair.mono (fun m hm => hm.1)
    have hHi : ∀ᶠ m in atTop,
        y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ∈
        Icc (α / 2) (β + α / 2) :=
      hPair.mono (fun m hm => hm.2)
    have hGapConv : Tendsto (fun m =>
        (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
          y m ω) atTop (𝓝 (0 : ℝ)) := by
      convert hInc using 1 <;> ext m <;> ring
    exact avram_ga_a28_compact_modulus_last_increment
      w (α / 2) (β + α / 2) (fun m => y m ω)
      (fun m => y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
      hmod hLo hHi hGapConv
  have hAbs : ∀ᵐ ω ∂P, Tendsto (fun m =>
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)|) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hWae] with ω h
    simpa only [abs_zero] using h.abs
  have hBound (m : ℕ) : ∀ᵐ ω ∂P,
      ‖|w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)|‖ ≤ B ω := by
    filter_upwards [hDom m] with ω hd
    simpa only [Real.norm_eq_abs, abs_abs] using hd
  have hDCT := tendsto_integral_of_dominated_convergence B hMeas hBI hBound hAbs
  simpa only [integral_zero] using hDCT
