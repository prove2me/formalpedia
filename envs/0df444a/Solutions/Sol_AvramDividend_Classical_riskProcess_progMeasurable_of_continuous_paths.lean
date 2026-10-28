-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_progMeasurable_of_continuous_paths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:28:43.584878+00:00
-- url     : https://prove2.me/submissions/62844396-f394-4b93-ac9f-f68ff6e82ba5

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Continuous-path adapted risk and dividends give a progressive controlled reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hXCont : ∀ ω, Continuous (fun t => X.X t ω))
    (hDCont : ∀ ω, Continuous (fun t => D t ω)) :
    ProgMeasurable 𝓕 (riskProcess X x D) := by
  have hXStrong : StronglyAdapted 𝓕 X.X :=
    X.adapted.stronglyAdapted
  have hDStrong : StronglyAdapted 𝓕 D :=
    hD.2.2.2.stronglyAdapted
  have hXProg : ProgMeasurable 𝓕 X.X :=
    hXStrong.progMeasurable_of_continuous hXCont
  have hDProg : ProgMeasurable 𝓕 D :=
    hDStrong.progMeasurable_of_continuous hDCont
  have hConst : ProgMeasurable 𝓕 (fun (_ : ℝ≥0) (_ : Ω) => x) :=
    isStronglyProgressive_const 𝓕 x
  have hSum : ProgMeasurable 𝓕 (fun t ω => x + X.X t ω) :=
    IsStronglyProgressive.add hConst hXProg
  have hDiff : ProgMeasurable 𝓕
      (fun t ω => x + X.X t ω - D t ω) :=
    IsStronglyProgressive.sub hSum hDProg
  unfold riskProcess
  exact hDiff
