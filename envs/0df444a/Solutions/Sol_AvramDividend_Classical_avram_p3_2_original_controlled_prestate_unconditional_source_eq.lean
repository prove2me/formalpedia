-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_controlled_prestate_unconditional_source_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:22:00.382528+00:00
-- url     : https://prove2.me/submissions/abdb64d4-0e82-42c5-8494-d0cea0da2ddb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_explicit_source_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual controlled original Lévy reserve's positive-time left
prestate is exactly leftLim X minus the pre-rightpayment dividend value.
The original Lévy cadlag property eliminates any assumed left limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t -
        D t ω := by
  exact avram_p3_2_original_controlled_left_prestate_explicit_source_eq
    X x D hD ω t ht
    (Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
    ((avram_p2_a_zero_rate_original_cadlag_regular_all_times X ω).1 t)
