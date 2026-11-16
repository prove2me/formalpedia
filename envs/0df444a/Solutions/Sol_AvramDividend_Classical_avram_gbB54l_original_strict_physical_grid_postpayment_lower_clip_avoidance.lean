-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54l_original_strict_physical_grid_postpayment_lower_clip_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:37:36.914471+00:00
-- url     : https://prove2.me/submissions/1dfd4fb5-5151-45d8-8dce-5ae8aafeb721

import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n m : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ ω (i : ℕ), (i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) < ρ ω →
      δ / 2 ≤ x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) ω := by
  intro ω i hi
  let t : ℝ≥0 := (i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))
  change δ / 2 ≤ x + X.X t ω - rightLimit D t ω
  have hb : δ ≤ x + X.X t ω - rightLimit D t ω :=
    (avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω (ρ ω) δ (hFloor ω)) t hi
  linarith
