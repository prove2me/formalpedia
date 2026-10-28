-- Prove2me | solution 2 for AvramDividend.Classical.survived_nextRecord_shifted_path_lower_guard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:21:51.039234+00:00
-- url     : https://prove2.me/submissions/90eff699-5b57-4826-b7c3-8454dc88cdeb

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + ε < X.X r ω), (r : ℝ≥0∞)))
    (hSurvive : (v : ℝ≥0∞) < barrierRuinTime X a ω) :
    ∀ s : ℝ≥0, u + s < v →
      -a ≤ X.X (u + s) ω - X.X u ω := by
  have hpeakU := firstUpcrossing_attains_peak X b hb ω u hu
  have hrecordU := firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u hu
  have hSu : runningSup X u ω = X.X u ω := by
    linarith [hrecordU]
  have hbε : 0 ≤ b + ε := add_nonneg hb hε
  have hSafe :=
    (firstUpcrossing_before_barrierRuin_iff_prefix_survival
      X a (b + ε) ha hbε ω v hv).mp hSurvive
  intro s hs
  have hs0 : u ≤ u + s := le_add_of_nonneg_right (by exact zero_le)
  have hSup : runningSup X u ω ≤ runningSup X (u + s) ω :=
    (runningSup_monotone_and_path_le X ω).1 hs0
  have hDraw : reflectedSup X (u + s) ω ≤ a :=
    hSafe (u + s) hs
  change runningSup X (u + s) ω - X.X (u + s) ω ≤ a at hDraw
  linarith
