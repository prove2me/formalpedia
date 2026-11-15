-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:46:03.012988+00:00
-- url     : https://prove2.me/submissions/7871b710-771c-4ea4-8659-a549a082906a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) =
    ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  let C : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun a b =>
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc a b ×ˢ B) ∂P)
  change C s t = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B
  have ht : s + (t - s) = t := by
    simpa only [add_comm] using (tsub_add_cancel_of_le hst)
  have hShift : C s (s + (t - s)) = C 0 (t - s) := by
    simpa only [C] using
      AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
        X s (t - s) B hB
  have hBase : C 0 (t - s) = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    simpa only [C] using
      AvramDividend.Classical.avram_ja34_original_all_negative_borel_expected_count_exact
        X (t - s) B hB hNeg
  calc
    C s t = C s (s + (t - s)) := by rw [ht]
    _ = C 0 (t - s) := hShift
    _ = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := hBase
