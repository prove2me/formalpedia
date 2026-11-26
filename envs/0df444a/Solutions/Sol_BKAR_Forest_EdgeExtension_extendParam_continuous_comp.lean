-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.extendParam_continuous_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:24.89723+00:00
-- url     : https://prove2.me/submissions/ac84305e-875e-4bda-bc2e-d5635596ac5a

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_ListPathContinuous_comp
import Theorems.Thm_BKAR_Forest_EdgeExtension_mem_old_of_mem_of_ne


set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution
    {X : Type*} [TopologicalSpace X] (h : EdgeExtension F F' e)
    {uPath : X → F.EdgeParam → ℝ} (hu : Continuous uPath)
    {tPath : X → ℝ} (ht : Continuous tPath) :
    Continuous (fun x : X => h.extendParam (uPath x) (tPath x)) := by
  apply continuous_pi
  intro e'
  by_cases he' : e'.val = e
  · have hfun :
        (fun x : X => h.extendParam (uPath x) (tPath x) e') =
          tPath := by
      funext x
      rw [extendParam, dif_pos he']
    rw [hfun]
    exact ht
  · have hfun :
        (fun x : X => h.extendParam (uPath x) (tPath x) e') =
          fun x : X =>
            uPath x ⟨e'.val, h.mem_old_of_mem_of_ne e'.property he'⟩ := by
      funext x
      rw [extendParam, dif_neg he']
    rw [hfun]
    exact
      (continuous_apply
        ⟨e'.val, h.mem_old_of_mem_of_ne e'.property he'⟩).comp hu
end BKAR.Forest.EdgeExtension
