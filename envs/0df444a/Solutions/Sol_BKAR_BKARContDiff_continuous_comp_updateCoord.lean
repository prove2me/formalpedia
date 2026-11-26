-- Prove2me | solution 1 for BKAR.BKARContDiff.continuous_comp_updateCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:47.726434+00:00
-- url     : https://prove2.me/submissions/e45a8753-0ce8-4b10-9652-6ea12c1df22c

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_BKARContDiff_continuous
import Theorems.Thm_BKAR_BKARContDiff_comp_updateCoord

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR
namespace BKARContDiff
theorem _root_.solution
    {ρ : (Edge V → ℝ) → ℝ} (hρ : BKARContDiff ρ)
    (x : Edge V → ℝ) (e : Edge V) :
    Continuous (fun t : ℝ => ρ (updateCoord x e t)) :=
  (hρ.comp_updateCoord x e).continuous
end BKARContDiff
end BKAR
