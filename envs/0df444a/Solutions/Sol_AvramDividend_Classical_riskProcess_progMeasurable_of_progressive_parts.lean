-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_progMeasurable_of_progressive_parts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:35:13.896085+00:00
-- url     : https://prove2.me/submissions/2332ff97-4d60-42e1-9a25-acaafa62690d

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The controlled reserve is progressive whenever both its stochastic components are. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hXProg : ProgMeasurable 𝓕 X.X)
    (hDProg : ProgMeasurable 𝓕 D) :
    ProgMeasurable 𝓕 (riskProcess X x D) := by
  have hConst : ProgMeasurable 𝓕 (fun (_ : ℝ≥0) (_ : Ω) => x) :=
    isStronglyProgressive_const 𝓕 x
  have hSum : ProgMeasurable 𝓕 (fun t ω => x + X.X t ω) :=
    IsStronglyProgressive.add hConst hXProg
  have hDiff : ProgMeasurable 𝓕
      (fun t ω => x + X.X t ω - D t ω) :=
    IsStronglyProgressive.sub hSum hDProg
  unfold riskProcess
  exact hDiff
