-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_stopped_W_le_source_X
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:08:28.389348+00:00
-- url     : https://prove2.me/submissions/5e88ab39-a81f-4d3f-ab84-cb3516376176

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- No admissible original dividend increases the stopped reserve above
    the uncompensated raw Lévy capital, even at ruin and payment jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, W ω ≤ x + X.X (τ ω) ω := by
  intro ω
  have hD0 : 0 ≤ D (τ ω) ω :=
    dividendStrategy_path_nonneg D hD.1.1 ω (τ ω)
  have hDright : D (τ ω) ω ≤ rightLimit D (τ ω) ω :=
    dividendStrategy_le_rightLimit D hD.1.1 ω (τ ω)
  rw [hW ω]
  split_ifs with h
  · linarith
  · dsimp [riskProcess]
    linarith