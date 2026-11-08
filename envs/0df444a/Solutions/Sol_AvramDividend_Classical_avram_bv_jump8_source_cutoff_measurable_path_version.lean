-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_source_cutoff_measurable_path_version
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:51:37.655548+00:00
-- url     : https://prove2.me/submissions/8deb1cad-4d91-4293-a86b-f1adb6b029d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_intrinsic_weighted_cutoff_borel
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_actual_source_weighted_cutoff_shift
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ), ∃ F : (ℝ≥0 → ℝ) → ℝ,
      Measurable F ∧ (∀ f, 0 ≤ F f ∧ F f ≤ 1) ∧
      (∀ᵐ ω ∂P, F (fun t : ℝ≥0 => X.X t ω) =
        Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))) ∧
      (∀ᵐ ω ∂P,
        F (fun t : ℝ≥0 => X.X ((n : ℝ≥0) + t) ω - X.X (n : ℝ≥0) ω) =
        Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))) := by
  intro n k
  obtain ⟨F, hFmeas, hFrange, hFpath⟩ :=
    avram_bv_jump8_cadlag_intrinsic_weighted_cutoff_borel k
  refine ⟨F, hFmeas, hFrange, ?_, ?_⟩
  · filter_upwards [] with ω
    exact hFpath _ (X.rightCont ω) (X.leftLim ω)
  · filter_upwards [] with ω
    obtain ⟨hRC, hLL⟩ :=
      avram_wave7_01_original_shifted_future_increment_path_cadlag
        X ω (n : ℝ≥0)
    rw [hFpath _ hRC hLL,
      avram_bv_jump8_actual_source_weighted_cutoff_shift X ω n k]
