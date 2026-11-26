-- Prove2me | solution 1 for BKAR.BKARContDiff.comp_updateCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:00.813039+00:00
-- url     : https://prove2.me/submissions/9d10e3a5-23e3-4e83-88a2-97b6000b19f6

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_ListPathContinuous_comp
import Theorems.Thm_BKAR_updateCoord_contDiff

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR
namespace BKARContDiff
theorem _root_.solution
    {ρ : (Edge V → ℝ) → ℝ} (hρ : BKARContDiff ρ)
    (x : Edge V → ℝ) (e : Edge V) :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun t : ℝ => ρ (updateCoord x e t)) :=
  hρ.contDiff.comp (updateCoord_contDiff x e)
end BKARContDiff
end BKAR
