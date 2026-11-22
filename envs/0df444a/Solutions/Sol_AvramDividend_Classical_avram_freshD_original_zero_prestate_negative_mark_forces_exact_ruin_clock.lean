-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_zero_prestate_negative_mark_forces_exact_ruin_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T09:12:53.086358+00:00
-- url     : https://prove2.me/submissions/0ec00d61-a347-45c8-818c-74339248248c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ ruinTime X x D ω)
    (hzero : x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω = 0)
    (hz : X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t < 0) :
    (t : ℝ≥0∞) = ruinTime X x D ω := by
  have hneg : riskProcess X x D t ω < 0 := by
    dsimp [riskProcess]
    linarith
  have hruin : ruinTime X x D ω ≤ (t : ℝ≥0∞) := by
    unfold ruinTime
    exact iInf_le_of_le t (iInf_le_of_le hneg le_rfl)
  exact le_antisymm ht hruin
