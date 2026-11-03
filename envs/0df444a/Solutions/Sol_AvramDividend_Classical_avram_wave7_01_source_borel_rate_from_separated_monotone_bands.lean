-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_source_borel_rate_from_separated_monotone_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:11:29.80518+00:00
-- url     : https://prove2.me/submissions/b24faaa7-a784-4e36-9d4d-8caea7877afb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_expected_count_monotone_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Extend genuine original-source separated-band Lévy intensities to the
exhaustive Borel mark set without any finite-activity hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (D : Set ℝ)
    (B : ℕ → Set ℝ) (hBm : ∀ n, MeasurableSet (B n))
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = D)
    (hSep : ∀ n, ∃ ε : ℝ, 0 < ε ∧ B n ⊆ Iic (-ε))
    (hBandRate : ∀ n,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B n) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B n)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ D) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν D := by
  classical
  have hCount :=
    avram_wave6_01_original_past_marked_expected_count_monotone_limit
      X s t hst Set.univ MeasurableSet.univ B hBm hBmono
  have hNu : X.ν (⋃ n, B n) = ⨆ n, X.ν (B n) :=
    hBmono.measure_iUnion
  rw [← hBcover]
  calc
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ (⋃ n, B n)) ∂P) =
        ⨆ n, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B n) ∂P) := by
          simpa only [Measure.restrict_univ] using hCount
    _ = ⨆ n, ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B n) := by
      simp_rw [hBandRate]
    _ = ((t - s : ℝ≥0) : ℝ≥0∞) * (⨆ n, X.ν (B n)) := by
      rw [ENNReal.mul_iSup]
    _ = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (⋃ n, B n) := by
      rw [hNu]
