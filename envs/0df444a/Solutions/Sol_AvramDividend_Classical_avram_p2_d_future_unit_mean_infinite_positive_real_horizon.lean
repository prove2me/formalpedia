-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_unit_mean_infinite_positive_real_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:37:34.91107+00:00
-- url     : https://prove2.me/submissions/9b4f4931-b9fd-4160-97c0-1b49508b3f1d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_nat_multiple

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Infinite first-unit mean of literal original marked jumps persists on every
positive physical time interval, with no asserted Lévy ν intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) (hpos : 0 < t)
    (hunit : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = ⊤) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) = ⊤ := by
  let M : ℝ≥0 → ℝ≥0∞ := fun q => (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 q ×ˢ B) ∂P)
  have ht0 : t ≠ 0 := ne_of_gt hpos
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 : ℝ≥0) / t)
  have htn : (1 : ℝ≥0) ≤ (n : ℝ≥0) * t := by
    calc
      (1 : ℝ≥0) = ((1 : ℝ≥0) / t) * t := by field_simp [ht0]
      _ ≤ (n : ℝ≥0) * t := mul_le_mul_of_nonneg_right hn.le (bot_le : (0 : ℝ≥0) ≤ t)
  have hMono : M 1 ≤ M ((n : ℝ≥0) * t) := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_monotone
        X 1 ((n : ℝ≥0) * t) htn B)
  have hNat : M ((n : ℝ≥0) * t) = (n : ℝ≥0∞) * M t := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_nat_multiple X B hB t n)
  have hTop : (n : ℝ≥0∞) * M t = ⊤ := by
    apply top_unique
    calc
      (⊤ : ℝ≥0∞) = M 1 := by simpa only [M] using hunit.symm
      _ ≤ M ((n : ℝ≥0) * t) := hMono
      _ = (n : ℝ≥0∞) * M t := hNat
  change M t = ⊤
  by_contra hne
  have htFinite : M t < ⊤ := lt_top_iff_ne_top.mpr hne
  have hProdFinite : (n : ℝ≥0∞) * M t < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) htFinite
  exact (ne_of_lt hProdFinite) hTop
