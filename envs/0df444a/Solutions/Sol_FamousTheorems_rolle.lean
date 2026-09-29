-- Prove2me | solution 1 for FamousTheorems.rolle
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T01:51:16.380432+00:00
-- url     : https://prove2.me/submissions/cb400b77-8202-4f73-977c-f7488b2462cb

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem solution {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Set.Ioo a b, deriv f c = 0 := exists_deriv_eq_zero hab hfc hfI
