-- Prove2me | solution 1 for BKAR.Forest.interpWithFill_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:03.7578+00:00
-- url     : https://prove2.me/submissions/f9719efb-2f72-44a2-9e06-e4363d1a4320

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
open BKAR.Forest
variable (F : Forest V)
namespace BKAR.Forest
theorem _root_.solution (u : F.EdgeParam → ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (F.interpWithFill u) := by
  rw [contDiff_pi]
  intro e
  by_cases h : F.inSameComponent e.left e.right
  · have hfun :
        (fun t : ℝ => F.interpWithFill u t e) =
          fun _ : ℝ => F.pathMin u (F.pathInF e.left e.right h) := by
      funext t
      rw [interpWithFill, dif_pos h]
    rw [hfun]
    exact contDiff_const
  · have hfun :
        (fun t : ℝ => F.interpWithFill u t e) = id := by
      funext t
      rw [interpWithFill, dif_neg h]
      rfl
    rw [hfun]
    exact contDiff_id
end BKAR.Forest
