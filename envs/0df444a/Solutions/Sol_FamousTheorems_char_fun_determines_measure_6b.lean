-- Prove2me | solution 1 for FamousTheorems.char_fun_determines_measure_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:27:58.221+00:00
-- url     : https://prove2.me/submissions/b514fa39-57ae-49fe-9542-3ce03ab82c05

import Mathlib

open MeasureTheory

theorem solution {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFun μ = charFun ν) : μ = ν :=
  Measure.ext_of_charFun h
