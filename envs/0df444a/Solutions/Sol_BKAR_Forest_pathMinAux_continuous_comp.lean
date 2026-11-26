-- Prove2me | solution 1 for BKAR.Forest.pathMinAux_continuous_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:05.868291+00:00
-- url     : https://prove2.me/submissions/493e1f7d-a025-4589-ada6-0565b67b7f89

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_Forest_paramValue_continuous_comp
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same



set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest
variable (F : Forest V)
namespace BKAR.Forest
theorem _root_.solution
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) {aPath : X → ℝ} (ha : Continuous aPath)
    (γ : List (Edge V)) :
    Continuous (fun x : X => F.pathMinAux (uPath x) (aPath x) γ) := by
  induction γ generalizing aPath with
  | nil =>
      simpa [pathMinAux] using ha
  | cons e γ ih =>
      have hmin :
          Continuous
            (fun x : X => min (aPath x) (F.paramValue (uPath x) e)) :=
        ha.min (F.paramValue_continuous_comp hu e)
      simpa [pathMinAux] using
        ih (aPath := fun x : X => min (aPath x) (F.paramValue (uPath x) e))
          hmin
end BKAR.Forest
