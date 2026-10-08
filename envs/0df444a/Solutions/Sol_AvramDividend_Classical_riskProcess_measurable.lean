-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:50:34.762985+00:00
-- url     : https://prove2.me/submissions/d941ae78-7de0-4cb5-8ca1-94984d87c096

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) :
    Measurable (fun ω => riskProcess X x D t ω) := by
  unfold riskProcess
  exact (measurable_const.add X.adapted.measurable).sub hD.2.2.2.measurable
