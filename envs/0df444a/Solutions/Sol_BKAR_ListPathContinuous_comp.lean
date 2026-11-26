-- Prove2me | solution 1 for BKAR.ListPathContinuous.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:22:45.608639+00:00
-- url     : https://prove2.me/submissions/a975c645-7f13-4613-8501-cce2d5293453

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
theorem _root_.solution {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : Nat} {tsPath : X → List ℝ}
    (hts : ListPathContinuous n tsPath) {f : Y → X} (hf : Continuous f) :
    ListPathContinuous n (fun y : Y => tsPath (f y)) := by
  constructor
  · intro y
    exact hts.1 (f y)
  · intro i
    exact (hts.2 i).comp hf
end BKAR.ListPathContinuous
