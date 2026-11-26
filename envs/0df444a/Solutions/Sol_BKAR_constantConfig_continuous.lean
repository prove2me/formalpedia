-- Prove2me | solution 1 for BKAR.constantConfig_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:19.442847+00:00
-- url     : https://prove2.me/submissions/d73c0bdd-d45c-4da7-8171-26c7edee6ac9

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_BKARContDiff_continuous
import Theorems.Thm_BKAR_constantConfig_contDiff

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR
theorem _root_.solution :
    Continuous (constantConfig (V := V)) :=
  constantConfig_contDiff.continuous
end BKAR
