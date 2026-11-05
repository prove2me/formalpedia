-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_negative_supported_original_mark_measure_full_borel_restriction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:05:44.726982+00:00
-- url     : https://prove2.me/submissions/3a3751f2-14fc-467b-949c-383b4b2c7dc2

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hZero : μ (Ici (0 : ℝ)) = 0) :
    μ B = μ (B ∩ Iio (0 : ℝ)) := by
  have hdiff : μ (B \ Ici (0 : ℝ)) = μ B := by
    exact measure_diff_null hZero
  simpa only [Set.diff_eq, Set.compl_Ici] using hdiff.symm
