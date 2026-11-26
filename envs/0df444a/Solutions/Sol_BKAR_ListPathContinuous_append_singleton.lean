-- Prove2me | solution 1 for BKAR.ListPathContinuous.append_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:03:32.542718+00:00
-- url     : https://prove2.me/submissions/6226b5a6-2044-4cae-8c64-232a0de0dc1c

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
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
open BKAR.ListPathContinuous
namespace BKAR.ListPathContinuous
theorem _root_.solution {X : Type*} [TopologicalSpace X]
    {n : Nat} {tsPath : X → List ℝ}
    (hts : ListPathContinuous n tsPath)
    {tPath : X → ℝ} (ht : Continuous tPath) :
    ListPathContinuous (n + 1) (fun x : X => tsPath x ++ [tPath x]) := by
  constructor
  · intro x
    simp [hts.1 x]
  · intro i
    by_cases hi : i < n
    · have hfun :
          (fun x : X => (tsPath x ++ [tPath x]).getD i 0) =
            fun x : X => (tsPath x).getD i 0 := by
        funext x
        rw [List.getD_append]
        rwa [hts.1 x]
      rw [hfun]
      exact hts.2 i
    · by_cases hin : i = n
      · subst i
        have hfun :
            (fun x : X => (tsPath x ++ [tPath x]).getD n 0) =
              tPath := by
          funext x
          rw [List.getD_append_right]
          · rw [hts.1 x]
            simp
          · rw [hts.1 x]
        rw [hfun]
        exact ht
      · have hni : n ≤ i := Nat.le_of_not_gt hi
        have hnlt : n < i := lt_of_le_of_ne hni (Ne.symm hin)
        have hs : n + 1 ≤ i := Nat.succ_le_of_lt hnlt
        have hfun :
            (fun x : X => (tsPath x ++ [tPath x]).getD i 0) =
              fun _ : X => 0 := by
          funext x
          exact List.getD_eq_default (l := tsPath x ++ [tPath x])
            (d := 0) (n := i) (by
              simpa [hts.1 x] using hs)
        rw [hfun]
        exact continuous_const
end BKAR.ListPathContinuous
