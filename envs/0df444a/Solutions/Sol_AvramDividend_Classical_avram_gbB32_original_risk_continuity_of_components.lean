-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB32_original_risk_continuity_of_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:47:22.890378+00:00
-- url     : https://prove2.me/submissions/b49eb70f-4a15-4d24-9a69-1a3917aaea14

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hX : ∀ ω, Continuous (fun t : ℝ≥0 => X.X t ω))
    (hD : ∀ ω, Continuous (fun t : ℝ≥0 => D t ω)) :
    ∀ ω, Continuous (fun t : ℝ≥0 => riskProcess X x D t ω) := by 
  intro ω
  change Continuous (fun t : ℝ≥0 => x + X.X t ω - D t ω)
  exact (continuous_const.add (hX ω)).sub (hD ω)
