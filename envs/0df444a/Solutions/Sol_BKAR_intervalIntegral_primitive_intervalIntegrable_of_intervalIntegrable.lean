-- Prove2me | solution 1 for BKAR.intervalIntegral_primitive_intervalIntegrable_of_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:15.734809+00:00
-- url     : https://prove2.me/submissions/f8ef8fca-5122-40f5-acd6-5c4031ee8d46

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
namespace BKAR
theorem _root_.solution
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable (fun x : ℝ => ∫ t in a..x, f t)
      MeasureTheory.volume a b :=
  (intervalIntegral.continuousOn_primitive_interval'
    (μ := MeasureTheory.volume) hf Set.left_mem_uIcc).intervalIntegrable
end BKAR
