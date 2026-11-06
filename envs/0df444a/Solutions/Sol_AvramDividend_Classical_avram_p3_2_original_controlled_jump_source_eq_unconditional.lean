-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_controlled_jump_source_eq_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:31:18.236585+00:00
-- url     : https://prove2.me/submissions/9501c36d-3df3-4718-b3f9-7f23e3ca9ca4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_postpayment_jump_source_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original controlled positive-time jump equals the actual Lévy
source jump minus the simultaneous right-dividend payment, without any
separately assumed cadlag limit or absence of coincident jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    (x + X.X t ω - rightLimit D t ω) -
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      (X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) -
          (rightLimit D t ω - D t ω) := by
  exact avram_p3_2_original_controlled_postpayment_jump_source_eq
    X x D hD ω t ht
    (Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
    ((avram_p2_a_zero_rate_original_cadlag_regular_all_times X ω).1 t)
