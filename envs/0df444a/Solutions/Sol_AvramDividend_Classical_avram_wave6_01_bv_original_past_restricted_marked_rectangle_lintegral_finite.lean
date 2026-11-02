-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_original_past_restricted_marked_rectangle_lintegral_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:50:06.52987+00:00
-- url     : https://prove2.me/submissions/6955c18f-57d4-441e-9da4-ee8cfbcd980d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Original-past restriction of a BV finite-activity marked jump
count is integrable and bounded by the genuine total source rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T)
    (s : ℝ≥0) (hst : s ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) ≤
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ∧
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) < ⊤ := by
  classical
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u))
  let J : Ω → ℝ≥0∞ := fun ω => N ω (Ioc s T ×ˢ B)
  let K : Ω → ℝ≥0∞ := fun ω => N ω (Ioc 0 T ×ˢ B)
  have hsub : Ioc s T ×ˢ B ⊆ Ioc 0 T ×ˢ B := by
    intro p hp
    exact ⟨⟨lt_of_le_of_lt (bot_le : (0 : ℝ≥0) ≤ s) hp.1.1, hp.1.2⟩, hp.2⟩
  have hPoint (ω : Ω) : J ω ≤ K ω := by
    exact measure_mono hsub
  have hAg : MeasurableSet A := (𝓕.le s) A hA
  have hRestrict :
      (∫⁻ ω in A, J ω ∂P) ≤ ∫⁻ ω, K ω ∂P := by
    calc
      _ = ∫⁻ ω, A.indicator J ω ∂P :=
        (lintegral_indicator hAg J).symm
      _ ≤ ∫⁻ ω, K ω ∂P := by
        apply lintegral_mono
        intro ω
        by_cases hω : ω ∈ A
        · simpa only [Set.indicator_of_mem hω] using hPoint ω
        · simp [Set.indicator, hω]
  obtain ⟨hRate, hFiniteK⟩ :=
    avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
      X hBV hFinite T hT grid hGrid hMesh hBound B hB
  change (∫⁻ ω in A, J ω ∂P) ≤
    (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ∧
      (∫⁻ ω in A, J ω ∂P) < ⊤
  exact ⟨hRestrict.trans hRate, lt_of_le_of_lt hRestrict hFiniteK⟩
