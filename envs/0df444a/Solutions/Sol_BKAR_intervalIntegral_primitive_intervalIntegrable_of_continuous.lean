-- Prove2me | solution 1 for BKAR.intervalIntegral_primitive_intervalIntegrable_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:09.474416+00:00
-- url     : https://prove2.me/submissions/58f904ce-a44c-48a7-96c2-c124c4ff072a

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_intervalIntegral_continuous_primitive_of_continuous

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR
theorem _root_.solution
    {f : ℝ → ℝ} (hf : Continuous f) (a b c : ℝ) :
    IntervalIntegrable (fun x : ℝ => ∫ t in a..x, f t)
      MeasureTheory.volume b c :=
  (intervalIntegral_continuous_primitive_of_continuous hf a).intervalIntegrable b c
end BKAR
