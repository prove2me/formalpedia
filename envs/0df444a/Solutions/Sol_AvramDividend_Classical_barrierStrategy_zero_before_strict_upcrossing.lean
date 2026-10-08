-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_zero_before_strict_upcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:29:28.812396+00:00
-- url     : https://prove2.me/submissions/f2df0d3c-ab9c-4a9c-a3bb-f96470ff70e9

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
    barrierStrategy X x a t ω = 0 := by
  classical
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
