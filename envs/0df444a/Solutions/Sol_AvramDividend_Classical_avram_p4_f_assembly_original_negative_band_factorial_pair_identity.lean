-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_negative_band_factorial_pair_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:37:37.473937+00:00
-- url     : https://prove2.me/submissions/74728db9-c56b-45be-bcb0-e1ab9d47c866

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let S : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let J : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    J = (F.card : ℝ≥0∞) ∧
      (F.card * (F.card - 1)) / 2 =
        ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
  classical
  dsimp
  constructor
  · have hCount :=
      avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
        X ω T n
    have hFin :=
      avram_wave7_06_original_negative_band_marked_times_finite X ω T n
    have hCard : ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard) = hFin.toFinset.card :=
      Set.ncard_eq_toFinset_card _ hFin
    simpa only [hCard] using hCount
  · simpa only [Finset.card_product_filter_lt, Nat.choose_two_right]
