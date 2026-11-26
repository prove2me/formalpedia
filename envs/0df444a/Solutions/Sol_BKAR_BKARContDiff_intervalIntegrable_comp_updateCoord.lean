-- Prove2me | solution 1 for BKAR.BKARContDiff.intervalIntegrable_comp_updateCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:33.392639+00:00
-- url     : https://prove2.me/submissions/3e1ca60f-f6c1-445d-bf17-7f3400e19dfa

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_BKARContDiff_continuous_comp_updateCoord

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR
namespace BKARContDiff
theorem _root_.solution
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (x : Edge V → ℝ) (e : Edge V)
    (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ρ (updateCoord x e t))
      MeasureTheory.volume a b :=
  (hρ.continuous_comp_updateCoord x e).intervalIntegrable a b
end BKARContDiff
end BKAR
