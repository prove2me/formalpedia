-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_rational_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:53:18.985876+00:00
-- url     : https://prove2.me/submissions/b6d80b5f-3e8e-4b19-8597-bb4f722b4f6f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_rational_relation
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A genuine original Lévy marked mean at an arbitrary horizon lies between
the rates of all enclosing rationally related horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (lo t hi : ℝ≥0) (n m d : ℕ) (hd : 0 < d)
    (hlo : (d : ℝ≥0) * lo = (n : ℝ≥0))
    (hhi : (d : ℝ≥0) * hi = (m : ℝ≥0))
    (hlot : lo ≤ t) (hthi : t ≤ hi) :
    ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) ≤
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) ∧
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) ≤
      ((m : ℝ≥0∞) / (d : ℝ≥0∞)) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by
  let M : ℝ≥0 → ℝ≥0∞ := fun q => (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 q ×ˢ B) ∂P)
  have hLo : M lo = ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * M 1 := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_rational_relation
        X B hB lo n d hd hlo)
  have hHi : M hi = ((m : ℝ≥0∞) / (d : ℝ≥0∞)) * M 1 := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_rational_relation
        X B hB hi m d hd hhi)
  have hMonoLo : M lo ≤ M t := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_monotone X lo t hlot B)
  have hMonoHi : M t ≤ M hi := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_monotone X t hi hthi B)
  change ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * M 1 ≤ M t ∧
    M t ≤ ((m : ℝ≥0∞) / (d : ℝ≥0∞)) * M 1
  constructor
  · calc
      ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * M 1 = M lo := hLo.symm
      _ ≤ M t := hMonoLo
  · calc
      M t ≤ M hi := hMonoHi
      _ = ((m : ℝ≥0∞) / (d : ℝ≥0∞)) * M 1 := hHi
