-- Prove2me | solution 1 for AvramDividend.Classical.avram_b65_original_strict_preruin_X_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:37:10.686261+00:00
-- url     : https://prove2.me/submissions/83385e31-77d0-4d3f-8f39-393e97a320bc

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_preruin_prepayment_reserve_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the original pre-ruin path the actual Levy source stays above the initial-capital floor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    -x ≤ X.X t ω := by
  have hRisk : 0 ≤ riskProcess X x D t ω :=
    avram_p3_2_original_strict_preruin_prepayment_reserve_nonnegative
      X x C D hD ω t ht
  have hDmono : Monotone (fun u : ℝ≥0 => D u ω) := hD.1.1.2.1 ω
  have hDzero : D 0 ω = 0 := hD.1.1.1 ω
  have hDnonneg : 0 ≤ D t ω := by
    have h0 := hDmono (show (0 : ℝ≥0) ≤ t from zero_le)
    simpa only [hDzero] using h0
  unfold riskProcess at hRisk
  linarith
