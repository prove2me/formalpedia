-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_prestate_marked_negative_rectangle_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:03:41.49128+00:00
-- url     : https://prove2.me/submissions/6cf36cb9-7452-411f-8e83-8e9874610dc3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original pre-jump compact reserve band times the negative
mark half-line is predictable by Borel, as needed for marked P2 counting. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (a b : ℝ) :
    MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      {p : ((ℝ≥0 × Ω) × ℝ) |
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
          p.1.1 ∈ Icc a b ∧ p.2 < 0} := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hA : MeasurableSet {p : ℝ≥0 × Ω |
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2)
        p.1 ∈ Icc a b} :=
    avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
      X x D hD a b
  have h1 : MeasurableSet {p : ((ℝ≥0 × Ω) × ℝ) |
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
        p.1.1 ∈ Icc a b} := hA.preimage measurable_fst
  have h2 : MeasurableSet {p : ((ℝ≥0 × Ω) × ℝ) | p.2 < 0} :=
    measurableSet_Iio.preimage measurable_snd
  exact h1.inter h2
