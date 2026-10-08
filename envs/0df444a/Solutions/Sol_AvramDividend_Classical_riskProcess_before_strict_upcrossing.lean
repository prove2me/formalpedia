-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_before_strict_upcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:30:47.251858+00:00
-- url     : https://prove2.me/submissions/1d4dee49-59a7-474d-b1f8-7d6d30bfeef2

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (t : ℝ≥0) (ω : Ω)
    (hpre : (t : ℝ≥0∞) <
        (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    riskProcess X x (barrierStrategy X x a) t ω = x + X.X t ω ∧
      (riskProcess X x (barrierStrategy X x a) t ω < 0 ↔ X.X t ω < -x) := by
  have hD : barrierStrategy X x a t ω = 0 := by
    apply barrierStrategy_zero_before_upcrossing X x a t ω
    intro s hst
    by_contra hnot
    have hcross : a - x < X.X s ω := lt_of_not_ge hnot
    have hinner :
        (⨅ (_ : a - x < X.X s ω), (s : ℝ≥0∞)) ≤
          (s : ℝ≥0∞) :=
      iInf_le (fun _ : a - x < X.X s ω => (s : ℝ≥0∞)) hcross
    have hup :
        (⨅ (u : ℝ≥0) (_ : a - x < X.X u ω), (u : ℝ≥0∞)) ≤
          (s : ℝ≥0∞) :=
      iInf_le_of_le s hinner
    have hst' : (s : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by
      exact_mod_cast hst
    exact (not_le_of_gt hpre) (hup.trans hst')
  have hU :
      riskProcess X x (barrierStrategy X x a) t ω = x + X.X t ω := by
    simp only [riskProcess, hD, sub_zero]
  constructor
  · exact hU
  · rw [hU]
    constructor
    · intro h
      linarith
    · intro h
      linarith
