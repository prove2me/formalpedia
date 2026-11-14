-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:26:56.184324+00:00
-- url     : https://prove2.me/submissions/7b59538c-68fc-4aeb-873c-fe22a1b90307

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a55_uniform_continuous_mesh_oscillation
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- True random original Gaussian physical crossing increments vanish almost surely by uniform source path continuity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun m => X.X (t m ω) ω - X.X (s m ω) ω)
      atTop (𝓝 (0 : ℝ)) := by
  filter_upwards
    [avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity X hν T,
      hRange, hGap] with ω hUC hR hG
  have hOsc :=
    avram_ga_a55_uniform_continuous_mesh_oscillation
      (fun u : ℝ≥0 => X.X u ω) T hUC
      (fun m (_ : ℕ) => s m ω)
      (fun m (_ : ℕ) => t m ω)
      (by intro m i; exact hR m)
      (by intro m i; exact hG m)
  apply Metric.tendsto_atTop.2
  intro ε hε
  rcases hOsc ε hε with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro m hm
  have h := hk m hm 0
  simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using h
