-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.extendParam_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:24.148964+00:00
-- url     : https://prove2.me/submissions/270fa242-fe9e-4cc6-8f05-c7719a0a40ef

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_Forest_EdgeExtension_mem_old_of_mem_of_ne


set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) :
    Continuous (fun t : ℝ => h.extendParam u t) := by
  apply continuous_pi
  intro e'
  by_cases he' : e'.val = e
  · have hfun :
        (fun t : ℝ => h.extendParam u t e') = id := by
      funext t
      rw [extendParam, dif_pos he']
      rfl
    rw [hfun]
    exact continuous_id
  · have hfun :
        (fun t : ℝ => h.extendParam u t e') =
          fun _ : ℝ => u ⟨e'.val, h.mem_old_of_mem_of_ne e'.property he'⟩ := by
      funext t
      rw [extendParam, dif_neg he']
    rw [hfun]
    exact continuous_const
end BKAR.Forest.EdgeExtension
