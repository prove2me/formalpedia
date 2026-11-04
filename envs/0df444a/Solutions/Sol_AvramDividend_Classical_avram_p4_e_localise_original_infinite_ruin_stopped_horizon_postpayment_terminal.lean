-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_infinite_ruin_stopped_horizon_postpayment_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:08:07.491875+00:00
-- url     : https://prove2.me/submissions/29519bda-11fd-4d13-b198-f5a6d930a314

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under infinite original ruin, the finite stopped horizon and rightpaid
    reserve are selected, with no killed-terminal convention. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, ruinTime X x D ω = ⊤ →
      τ ω = (n : ℝ≥0) ∧
      W ω = x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω := by
  intro ω hInf
  have hτn : τ ω = (n : ℝ≥0) := by
    rw [hτeq ω, hInf]
    simp
  constructor
  · exact hτn
  · have hStrict : (τ ω : ℝ≥0∞) < ruinTime X x D ω := by
      simp [hInf]
    have hBranch : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω :=
      Or.inr hStrict
    rw [hW ω, if_pos hBranch, hτn]
