-- Prove2me | solution 1 for AvramDividend.Classical.survived_nextRecord_shifted_path_lower_guard
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:21:49.450529+00:00
-- url     : https://prove2.me/submissions/09ebdc74-0850-4d46-85f7-7ad6e2ce9cf3

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

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
  intro s hs
  have hpre := (AvramDividend.Classical.firstUpcrossing_before_barrierRuin_iff_prefix_survival X a (b + ε) ha
    (by linarith) ω v hv).1 hSurvive (u + s) hs
  have h0 := AvramDividend.Classical.firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u hu
  have hmono := (AvramDividend.Classical.runningSup_monotone_and_path_le X ω).1 (le_self_add : u ≤ u + s)
  unfold reflectedSup at hpre
  linarith
