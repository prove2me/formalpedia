-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_allnu_unadjusted_reserve_identity_forces_zero_dividend_rightatom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:17:06.415204+00:00
-- url     : https://prove2.me/submissions/3a2e4e41-dbf3-45ab-9b87-997611bcb9b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Unadjusted prepayment/postpayment equality forces a zero right dividend jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (η : Ω),
      X.X u η = (u : ℝ) * X.c +
        (Y.X u η - (u : ℝ) * Y.c) + Jsmall u η + Jlarge u η)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) (ω : Ω)
    (hUnadjusted :
      riskProcess X x D t ω =
        x + ((t : ℝ) * X.c +
          (Y.X t ω - (t : ℝ) * Y.c) +
          Jsmall t ω + Jlarge t ω) - rightLimit D t ω) :
    rightLimit D t ω = D t ω := by
  simp only [riskProcess] at hUnadjusted
  rw [hSourceDecomp t ω] at hUnadjusted
  linarith
