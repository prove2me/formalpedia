-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_weighted_extracted_count_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:46:23.329458+00:00
-- url     : https://prove2.me/submissions/0358e471-4091-4438-897e-c42df66d3364

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_future_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Past nonnegative weights factor against any exact measurable extractor
of the original shifted Lévy future path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (N : Ω → ℝ≥0∞)
    (hExtract : ∀ ω : Ω,
      N ω = F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω))
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W) :
    (∫⁻ ω, W ω * N ω ∂P) =
      (∫⁻ ω, W ω ∂P) * (∫⁻ ω, N ω ∂P) := by
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω v => X.X (s + v) ω - X.X s ω
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω v => X.X v ω
  let rate : ℝ≥0∞ :=
    ∫⁻ y, F y ∂(Measure.map Z P)
  haveI : IsProbabilityMeasure P := X.isProbability
  have hH : Measurable[𝓕 s] (fun _ : Ω => ()) := measurable_const
  have hf : Measurable
      (fun p : Unit × (ℝ≥0 → ℝ) => F p.2) :=
    hF.comp measurable_snd
  have hAll : (∫⁻ ω, F (Y ω) ∂P) = rate := by
    simpa [Y, rate] using
      (avram_root29_01_original_future_kernel_past_test
        X s (fun _ : Ω => ()) hH Set.univ MeasurableSet.univ
        (fun p : Unit × (ℝ≥0 → ℝ) => F p.2) hf)
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro v
    exact (X.adapted v).mono (𝓕.le v) le_rfl
  have hMap : (∫⁻ ω, F (Z ω) ∂P) = rate :=
    (lintegral_map hF hZ).symm
  have hWeight : (∫⁻ ω, W ω * F (Y ω) ∂P) =
      (∫⁻ ω, W ω ∂P) * (∫⁻ ω, F (Z ω) ∂P) := by
    exact avram_p2_e_compensator_weighted_future_kernel
      X s W hW F hF
  have hN : (∫⁻ ω, N ω ∂P) = rate := by
    calc
      (∫⁻ ω, N ω ∂P) =
          (∫⁻ ω, F (Y ω) ∂P) := by
            exact lintegral_congr hExtract
      _ = rate := hAll
  have hNW : (∫⁻ ω, W ω * N ω ∂P) =
      (∫⁻ ω, W ω * F (Y ω) ∂P) := by
    apply lintegral_congr
    intro ω
    rw [hExtract ω]
  calc
    (∫⁻ ω, W ω * N ω ∂P) =
        (∫⁻ ω, W ω * F (Y ω) ∂P) := hNW
    _ = (∫⁻ ω, W ω ∂P) *
        (∫⁻ ω, F (Z ω) ∂P) := hWeight
    _ = (∫⁻ ω, W ω ∂P) * rate := by
        rw [hMap]
    _ = (∫⁻ ω, W ω ∂P) * (∫⁻ ω, N ω ∂P) := by
        rw [hN]
