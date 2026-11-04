-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_marked_grid_lintegral_to_void_intensity_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:00:08.915837+00:00
-- url     : https://prove2.me/submissions/39d27ebd-ba77-4a33-b122-135c9da49f90

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_occupied_count_lintegral_dct_of_eventual_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Dominated source grid occupation identifies the original infinitesimal void rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (void : ℝ≥0 → ENNReal)
    (hVoid : ∀ s, void s =
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0})
    (K : ℕ → Ω → ENNReal) (N : Ω → ENNReal)
    (hK : ∀ m, Measurable (K m))
    (hBound : ∀ m ω, K m ω ≤ N ω)
    (hInt : (∫⁻ ω, N ω ∂P) < ⊤)
    (hEvent : ∀ ω, ∀ᶠ m in (Filter.atTop : Filter ℕ),
      K m ω = N ω)
    (hGridMean : ∀ m,
      (∫⁻ ω, K m ω ∂P).toReal =
        (m : ℝ) * (1 - (void (T / (m : ℝ≥0))).toReal))
    (hRate : (∫⁻ ω, N ω ∂P).toReal =
      (T : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal) :
    Filter.Tendsto
      (fun m : ℕ => (m : ℝ) *
        (1 - (void (T / (m : ℝ≥0))).toReal))
      Filter.atTop (nhds ((T : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)) := by
  have hDCT :=
    avram_wave7_06_occupied_count_lintegral_dct_of_eventual_eq
      P K N hK hBound hInt hEvent
  have hfin : (∫⁻ ω, N ω ∂P) ≠ ⊤ := ne_top_of_lt hInt
  have hReal : Filter.Tendsto
      (fun m : ℕ => (∫⁻ ω, K m ω ∂P).toReal)
      Filter.atTop
      (nhds (∫⁻ ω, N ω ∂P).toReal) :=
    (ENNReal.continuousAt_toReal hfin).tendsto.comp hDCT
  simpa only [hGridMean, hRate] using hReal
