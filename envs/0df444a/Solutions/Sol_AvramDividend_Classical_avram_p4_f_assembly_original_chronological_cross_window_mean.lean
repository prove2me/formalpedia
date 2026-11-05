-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_chronological_cross_window_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:55:49.148199+00:00
-- url     : https://prove2.me/submissions/9786deb1-91ef-4be0-9a93-6cc1824ad047

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_weighted_from_zero_origin_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ) :
    let Jpast : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Jfuture : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    (∫⁻ ω, Jpast ω * Jfuture ω ∂P) =
      (∫⁻ ω, Jpast ω ∂P) *
        (((t - s : ℝ≥0) : ℝ≥0∞) *
          X.ν (Iic (-(1 / ((n : ℝ) + 1))))) := by
  dsimp only
  exact avram_p2_e_compensator_public_weighted_from_zero_origin_rate
    X s t hst (Iic (-(1 / ((n : ℝ) + 1)))) measurableSet_Iic
    (fun ω : Ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))))
    (avram_p4_f_assembly_original_past_count_raw_measurable_auto X s n)
