-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB171_original_dividend_locally_bounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:37:45.899478+00:00
-- url     : https://prove2.me/submissions/4f9b8435-77aa-483e-a3d6-c1bea8590844

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    LocallyBoundedVariationOn (fun t : ℝ≥0 => D t ω) Set.univ := by
  have hmono : Monotone (fun t : ℝ≥0 => D t ω) := hD.2.1 ω
  exact (hmono.monotoneOn Set.univ).locallyBoundedVariationOn
