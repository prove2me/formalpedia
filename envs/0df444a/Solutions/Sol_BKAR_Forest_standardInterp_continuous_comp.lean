-- Prove2me | solution 1 for BKAR.Forest.standardInterp_continuous_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:39.571043+00:00
-- url     : https://prove2.me/submissions/586181dd-2900-44b4-8f26-9ccbbe4f4e8e

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_Forest_pathMin_continuous_comp

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest
variable (F : Forest V)
namespace BKAR.Forest
theorem _root_.solution
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) :
    Continuous (fun x : X => F.standardInterp (uPath x)) := by
  apply continuous_pi
  intro e
  by_cases h : F.inSameComponent e.left e.right
  · have hfun :
        (fun x : X => F.standardInterp (uPath x) e) =
          fun x : X => F.pathMin (uPath x) (F.pathInF e.left e.right h) := by
      funext x
      rw [standardInterp, dif_pos h]
    rw [hfun]
    exact F.pathMin_continuous_comp hu (F.pathInF e.left e.right h)
  · have hfun :
        (fun x : X => F.standardInterp (uPath x) e) =
          fun _ : X => (0 : ℝ) := by
      funext x
      rw [standardInterp, dif_neg h]
    rw [hfun]
    exact continuous_const
end BKAR.Forest
