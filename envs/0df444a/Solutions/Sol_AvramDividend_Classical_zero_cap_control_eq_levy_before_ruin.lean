-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_control_eq_levy_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:30:03.477992+00:00
-- url     : https://prove2.me/submissions/b7f93f60-9558-46c6-b30a-8f6d6774f6fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical



theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (t : ℝ≥0) (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < ruinTime X 0 D ω) :
    D t ω = X.X t ω := by
  have h1 := hD.2 ω t ht0
  rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
  have h2 : ¬ riskProcess X 0 D t ω < 0 := by
    intro hlt
    have : ruinTime X 0 D ω ≤ (t : ℝ≥0∞) := iInf₂_le t hlt
    exact absurd ht (not_lt.mpr this)
  unfold riskProcess at h1 h2
  linarith

