-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys116_original_admissible_dividend_ae_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:09:48.622665+00:00
-- url     : https://prove2.me/submissions/8ef7b733-efb0-4107-a51f-e5d489bb2cbc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- An original admissible dividend path is continuous at
Lebesgue-almost every time, since it is monotone. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (ω : Ω) :
    μ {t : ℝ≥0 | ¬ ContinuousAt (fun s : ℝ≥0 => D s ω) t} = 0 := by
  have hmono : Monotone (fun t : ℝ≥0 => D t ω) := hD.1.1.2.1 ω
  exact hmono.countable_not_continuousAt.measure_zero μ
