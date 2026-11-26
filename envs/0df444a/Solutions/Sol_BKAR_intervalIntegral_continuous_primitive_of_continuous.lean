-- Prove2me | solution 1 for BKAR.intervalIntegral_continuous_primitive_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:25:22.366181+00:00
-- url     : https://prove2.me/submissions/000580ca-e0cd-4dd0-ac18-4c7bc2ca8986

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
    {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Continuous (fun b : ℝ => ∫ t in a..b, f t) :=
  intervalIntegral.continuous_primitive
    (μ := MeasureTheory.volume) (fun a b => hf.intervalIntegrable a b) a
end BKAR
