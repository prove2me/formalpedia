-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:03:36.94743+00:00
-- url     : https://prove2.me/submissions/24b0fd8e-adc4-41f9-9544-6aa6cef29e6c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Adapted 𝓕 (riskProcess X x D) := by
  unfold riskProcess
  exact ((adapted_const 𝓕 x).add X.adapted).sub hD.2.2.2
