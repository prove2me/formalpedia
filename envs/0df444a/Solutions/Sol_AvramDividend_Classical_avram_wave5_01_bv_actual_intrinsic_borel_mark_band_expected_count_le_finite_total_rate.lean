-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:42:30.625079+00:00
-- url     : https://prove2.me/submissions/c33c5775-dcff-4481-b9ce-e0ff6ce16aa5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- All Borel marked source subcounts are L1-local in finite-activity BV. -/
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
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ((Ioc 0 T) ×ˢ B) ∂P) ≤
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ∧
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ((Ioc 0 T) ×ˢ B) ∂P) < ⊤ := by
  have hSub :
      ((Ioc 0 T) ×ˢ B) ⊆
      ((Ioc 0 T) ×ˢ (Set.univ : Set ℝ)) := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩
  have hBoundCount :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          ((Ioc 0 T) ×ˢ B) ∂P) ≤
        (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    calc
      _ ≤ ∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          ((Ioc 0 T) ×ˢ (Set.univ : Set ℝ)) ∂P :=
        lintegral_mono (fun ω => measure_mono hSub)
      _ = _ :=
        avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
          X hBV hFinite T hT grid hGrid hMesh hBound
  have hRateEq :
      ENNReal.ofReal ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg T),
      ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_toReal (ne_of_lt hFinite)]
  have hRateFinite :
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) < ⊤ := by
    rw [← hRateEq]
    exact ENNReal.ofReal_lt_top
  exact ⟨hBoundCount, lt_of_le_of_lt hBoundCount hRateFinite⟩
