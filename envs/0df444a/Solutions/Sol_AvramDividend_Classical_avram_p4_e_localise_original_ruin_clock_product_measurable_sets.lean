-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ruin_clock_product_measurable_sets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:15:44.220365+00:00
-- url     : https://prove2.me/submissions/adc27cf8-1b92-4016-a9d0-c7bf71e1bc4b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original random ruin-clock space-time threshold sets are product measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hDiv : IsDividendStrategy 𝓕 D) :
    MeasurableSet {p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) < ruinTime X x D p.2} ∧
    ∀ n : ℕ, MeasurableSet {p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) < min (ruinTime X x D p.2) (n : ℝ≥0∞)} := by
  have hRuin : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hDiv
  have hTime : Measurable (fun p : ℝ≥0 × Ω => (p.1 : ℝ≥0∞)) := by
    fun_prop
  have hRuinProd : Measurable (fun p : ℝ≥0 × Ω => ruinTime X x D p.2) :=
    hRuin.comp measurable_snd
  refine ⟨measurableSet_lt hTime hRuinProd, ?_⟩
  intro n
  have hMin : Measurable (fun p : ℝ≥0 × Ω =>
      min (ruinTime X x D p.2) (n : ℝ≥0∞)) :=
    hRuinProd.min measurable_const
  exact measurableSet_lt hTime hMin
