-- Prove2me | solution 1 for BianchiIX.measurable_rootExtension
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:41:08.29763+00:00
-- url     : https://prove2.me/submissions/9ca849c4-408d-4c45-8189-32d345e6c908

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_contDiff_rootPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX
noncomputable section


theorem solution {X : Type*} [MeasurableSpace X] {s d e x : X → ℝ}
    (hs : Measurable s) (hd : Measurable d) (he : Measurable e) (hx : Measurable x) :
    Measurable (fun q => rootExtension (s q) (d q) (e q) (x q)) :=
  hs.add (((he.mul hd).mul hs).mul (contDiff_rootPrimitive.continuous.measurable.comp ((he.mul hx).div hs)))
