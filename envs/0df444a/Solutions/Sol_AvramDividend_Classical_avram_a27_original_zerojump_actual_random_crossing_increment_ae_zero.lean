-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_zerojump_actual_random_crossing_increment_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:16:57.362036+00:00
-- url     : https://prove2.me/submissions/80f4e5ac-e6d6-4f1c-9e6d-9410fcd0c009

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a106_original_gaussian_true_random_crossing_value_modulus_from_positive_prefix
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1)) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      X.X (t m ω) ω - X.X (s m ω) ω) atTop (nhds (0 : ℝ))  := by
  have hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, u ∈ Icc ((1 : ℝ) / 2) (2 + 1 / 2) →
        v ∈ Icc ((1 : ℝ) / 2) (2 + 1 / 2) →
          |v - u| < δ → |v - u| < ε := by
    intro ε hε
    exact ⟨ε, hε, fun u v hu hv hd => hd⟩
  have hbase : ∀ᵐ ω ∂P, ∀ᶠ (m : ℕ) in atTop,
      (1 : ℝ) ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ (2 : ℝ) := by
    filter_upwards [] with ω
    filter_upwards [] with m
    norm_num
  have ht :=
    avram_ga_a106_original_gaussian_true_random_crossing_value_modulus_from_positive_prefix
      X hν T s t hRange hGap (1 : ℝ) (2 : ℝ)
      (by norm_num) (fun _ _ => (1 : ℝ))
      hbase (fun z : ℝ => z) hmod
  filter_upwards [ht] with ω hw
  simpa only [add_sub_cancel_left] using hw
