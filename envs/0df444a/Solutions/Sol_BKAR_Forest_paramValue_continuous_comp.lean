-- Prove2me | solution 1 for BKAR.Forest.paramValue_continuous_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:23:43.445566+00:00
-- url     : https://prove2.me/submissions/db0a564d-6eaa-435c-a4c7-a74c65d42411

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_ListPathContinuous_comp
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
attribute [local simp] BKAR.Forest.paramValue_of_mem



set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest
variable (F : Forest V)
namespace BKAR.Forest
theorem _root_.solution
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) (e : Edge V) :
    Continuous (fun x : X => F.paramValue (uPath x) e) := by
  by_cases he : e ∈ F.edges
  · have hfun :
        (fun x : X => F.paramValue (uPath x) e) =
          fun x : X => uPath x ⟨e, he⟩ := by
      funext x
      rw [paramValue_of_mem F (uPath x) he]
    rw [hfun]
    exact (continuous_apply ⟨e, he⟩).comp hu
  · have hfun :
        (fun x : X => F.paramValue (uPath x) e) =
          fun _ : X => (1 : ℝ) := by
      funext x
      rw [paramValue, dif_neg he]
    rw [hfun]
    exact continuous_const
end BKAR.Forest
