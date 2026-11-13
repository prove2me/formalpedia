-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_negative_borel_factorial_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:25:59.781064+00:00
-- url     : https://prove2.me/submissions/624a390d-7681-4639-a2e2-83ee8ecd3563

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_real_count_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let J : Ω → ℝ := fun ω => (N ω).toReal
    Integrable (fun ω => J ω * (J ω - 1)) P := by
  let J : Ω → ℝ := fun ω =>
    (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)).toReal
  change Integrable (fun ω => J ω * (J ω - 1)) P
  have hSq : Integrable (fun ω => J ω ^ 2) P := by
    simpa only [J] using
      avram_a20_original_negative_borel_real_count_square_integrable
        X hFinite T B hB hNeg
  have hFirst : Integrable J P := by
    simpa only [J] using
      (avram_ja35_original_negative_borel_real_count_first_moment
        X hFinite T B hB hNeg).1
  have hId : (fun ω => J ω * (J ω - 1)) =
      (fun ω => J ω ^ 2 - J ω) := by
    funext ω
    ring
  rw [hId]
  exact hSq.sub hFirst
