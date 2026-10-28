-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_successful_upcrossing_iff_raw_lower_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:55:23.550324+00:00
-- url     : https://prove2.me/submissions/47af4ca9-919d-4590-9fd8-7f37e98964d8

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinTime_eq_min_rawRuin_drawdownRuin
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_drawdown_survival_sandwich
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_strictly_before_drawdown_ruin
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Before an attained positive-barrier record, controlled and raw ruin
    give the same strict survival decision. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (u : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω ↔
      (u : ℝ≥0∞) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by
  classical
  rw [barrierStrategy_ruinTime_eq_min_rawRuin_drawdownRuin X x a hxa ω]
  constructor
  · intro h
    exact (lt_min_iff.mp h).1
  · intro hraw
    have hprefix : ∀ t : ℝ≥0, t < u → -x ≤ X.X t ω := by
      intro t ht
      by_contra hbad
      have hcross : X.X t ω < -x := lt_of_not_ge hbad
      have hle :
          (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞)) ≤
            (t : ℝ≥0∞) :=
        iInf_le_of_le t (iInf_le_of_le hcross le_rfl)
      have htu : (t : ℝ≥0∞) < (u : ℝ≥0∞) := by
        exact_mod_cast ht
      exact (not_lt_of_ge hle) (lt_trans htu hraw)
    have hbefore :
        ∀ t : ℝ≥0, t < u →
          runningSup X t ω - X.X t ω ≤ a := by
      apply (firstUpcrossing_drawdown_survival_sandwich X a
        (a - x) ω u hu).1
      intro t ht
      have hid : (a - x) - a = -x := by ring
      rw [hid]
      exact hprefix t ht
    have hdraw :
        (u : ℝ≥0∞) <
          (⨅ (t : ℝ≥0)
            (_ : a < runningSup X t ω - X.X t ω),
            (t : ℝ≥0∞)) := by
      have h := firstUpcrossing_strictly_before_drawdown_ruin
        X a (a - x) ha (sub_nonneg.mpr hxa) ω u hu
        (by
          intro t ht
          simpa only [reflectedSup] using hbefore t ht)
      simpa only [reflectedSup] using h
    exact lt_min hraw hdraw
