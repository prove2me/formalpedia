-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a111_original_gaussian_random_crossing_bounded_uniform_value_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:46:22.121355+00:00
-- url     : https://prove2.me/submissions/c800370f-6109-4f28-8a9a-66f7e87c416b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Uniformly bounded uniformly continuous compact-clipped value has vanishing expected L1 increments across any true randomly selected Gaussian crossing cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hW : ∀ z : ℝ, |w z| ≤ M)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, |v - u| < δ → |w v - w u| < ε)
    (y : ℕ → Ω → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)|) P) :
    Tendsto (fun m => ∫ ω,
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)| ∂P) atTop (𝓝 (0 : ℝ)) := by
  have hXae := avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
    X hν T s t hRange hGap
  have hWae : ∀ᵐ ω ∂P, Tendsto (fun m =>
      w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hXae] with ω hInc
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨δ,hδ,hMod⟩ := hmod ε hε
    obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.1 hInc) δ hδ
    refine ⟨N, ?_⟩
    intro m hm
    have hShort : |X.X (t m ω) ω - X.X (s m ω) ω| < δ := by
      simpa only [Real.dist_eq, sub_zero] using hN m hm
    have hVal := hMod (y m ω) (y m ω +
      (X.X (t m ω) ω - X.X (s m ω) ω)) (by
      simpa only [add_sub_cancel_left] using hShort)
    simpa only [Real.dist_eq, sub_zero] using hVal
  have hAbs : ∀ᵐ ω ∂P, Tendsto (fun m =>
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)|) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hWae] with ω h
    simpa only [abs_zero] using h.abs
  have hBound (m : ℕ) (ω : Ω) :
      ‖|w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)|‖ ≤ (2 * M) := by
    simp only [Real.norm_eq_abs, abs_abs]
    calc
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)| ≤
        |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))| +
          |w (y m ω)| := abs_sub _ _
      _ ≤ M + M := add_le_add (hW _) (hW _)
      _ = 2 * M := by ring
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun _ : Ω => 2 * M) hMeas (integrable_const _)
    (fun m => Filter.Eventually.of_forall (hBound m)) hAbs
  simpa only [integral_zero] using hDCT
