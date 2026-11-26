-- Prove2me | solution 1 for BKAR.Forest.interpWithFill_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:26.947805+00:00
-- url     : https://prove2.me/submissions/8d6ad735-5179-451c-9859-99ef9290e82e

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_BKARContDiff_continuous
import Theorems.Thm_BKAR_Forest_interpWithFill_contDiff

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest
variable (F : Forest V)
namespace BKAR.Forest
theorem _root_.solution (u : F.EdgeParam → ℝ) :
    Continuous (F.interpWithFill u) :=
  (F.interpWithFill_contDiff u).continuous
end BKAR.Forest
