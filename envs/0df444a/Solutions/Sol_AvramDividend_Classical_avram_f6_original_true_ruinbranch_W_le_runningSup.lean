-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_true_ruinbranch_W_le_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:50:40.142223+00:00
-- url     : https://prove2.me/submissions/8192704a-5268-41c3-97b8-d6e90509a25a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    (if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω) ≤
      x + runningSup X T ω := by
  have hrl : 0 ≤ rightLimit D t ω :=
    avram_ga_a35_original_dividend_rightLimit_nonnegative D hD t ω
  have hnonnegD : 0 ≤ D t ω := by
    have hmono := (hD.2.1 ω) (bot_le : (0 : ℝ≥0) ≤ t)
    have hzero : D (0 : ℝ≥0) ω = 0 := hD.1 ω
    change D (0 : ℝ≥0) ω ≤ D t ω at hmono
    simpa only [hzero] using hmono
  have hW : (if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω) ≤ x + X.X t ω := by
    split_ifs
    · linarith
    · dsimp [riskProcess]
      linarith
  have hsup := runningSup_monotone_and_path_le X ω
  have hle : X.X t ω ≤ runningSup X T ω :=
    le_trans (hsup.2 t) (hsup.1 ht)
  linarith
