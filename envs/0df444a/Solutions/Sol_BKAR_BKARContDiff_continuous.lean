-- Prove2me | solution 1 for BKAR.BKARContDiff.continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:22:54.081802+00:00
-- url     : https://prove2.me/submissions/8c5b4454-e605-4071-9a8d-77c76ee47490

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
open BKAR.BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution (hρ : BKARContDiff ρ) :
    Continuous ρ :=
  hρ.contDiff.continuous
end BKAR.BKARContDiff
