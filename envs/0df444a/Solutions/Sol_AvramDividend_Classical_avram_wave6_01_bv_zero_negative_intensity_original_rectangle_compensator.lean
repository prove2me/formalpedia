-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_zero_negative_intensity_original_rectangle_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:56:35.121197+00:00
-- url     : https://prove2.me/submissions/de82a2d9-b606-4160-a9af-40b4fb106d9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hZero : X.ν (Iio (0 : ℝ)) = 0)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n → StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i : ℕ,
      i < n → dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T)
    (s : ℝ≥0) (hst : s ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) =
      P A * ((T - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  classical
  have hFinite : X.ν (Iio (0 : ℝ)) < ⊤ := by
    rw [hZero]
    exact bot_lt_top
  have hνB : X.ν B = 0 := by
    have hsub : B ⊆ Iio (0 : ℝ) ∪ Ici (0 : ℝ) := by
      intro x hx
      by_cases hx0 : x < 0
      · exact Or.inl hx0
      · exact Or.inr (le_of_not_gt hx0)
    apply le_antisymm _ bot_le
    calc
      X.ν B ≤ X.ν (Iio (0 : ℝ) ∪ Ici (0 : ℝ)) :=
        measure_mono hsub
      _ ≤ X.ν (Iio (0 : ℝ)) + X.ν (Ici (0 : ℝ)) :=
        measure_union_le _ _
      _ = 0 := by rw [hZero, X.ν_Ici, zero_add]
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let J : Ω → ℝ≥0∞ := fun ω => N ω (Ioc s T ×ˢ B)
  let K : Ω → ℝ≥0∞ := fun ω => N ω (Ioc 0 T ×ˢ B)
  have hsub : Ioc s T ×ˢ B ⊆ Ioc 0 T ×ˢ B := by
    intro p hp
    exact ⟨⟨lt_of_le_of_lt (bot_le : (0 : ℝ≥0) ≤ s) hp.1.1, hp.1.2⟩, hp.2⟩
  have hPoint (ω : Ω) : J ω ≤ K ω := measure_mono hsub
  have hAg : MeasurableSet A := (𝓕.le s) A hA
  have hRestrict : (∫⁻ ω in A, J ω ∂P) ≤ ∫⁻ ω, K ω ∂P := by
    calc
      _ = ∫⁻ ω, A.indicator J ω ∂P :=
        (lintegral_indicator hAg J).symm
      _ ≤ ∫⁻ ω, K ω ∂P := by
        apply lintegral_mono
        intro ω
        by_cases hω : ω ∈ A
        · simpa only [Set.indicator_of_mem hω] using hPoint ω
        · simp [Set.indicator, hω]
  obtain ⟨hRate, _⟩ := avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
      X hBV hFinite T hT grid hGrid hMesh hBound B hB
  have hKzero : (∫⁻ ω, K ω ∂P) = 0 := by
    apply le_antisymm _ bot_le
    calc
      _ ≤ (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := hRate
      _ = 0 := by rw [hZero, mul_zero]
  have hJzero : (∫⁻ ω in A, J ω ∂P) = 0 :=
    le_antisymm (hRestrict.trans (le_of_eq hKzero)) bot_le
  change (∫⁻ ω in A, J ω ∂P) =
    P A * ((T - s : ℝ≥0) : ℝ≥0∞) * X.ν B
  simp [hJzero, hνB]
