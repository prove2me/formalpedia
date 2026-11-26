-- Prove2me | solution 1 for BKAR.ListPathContinuous.const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:03:44.176799+00:00
-- url     : https://prove2.me/submissions/4bca8594-e4f8-43d4-8cfa-ffd4ac57c9e9

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.ListPathContinuous
namespace BKAR.ListPathContinuous
theorem _root_.solution {X : Type*} [TopologicalSpace X] (ts : List ℝ) :
    ListPathContinuous ts.length (fun _ : X => ts) := by
  constructor
  · intro _x
    rfl
  · intro _i
    exact continuous_const
end BKAR.ListPathContinuous
