-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_lastSlice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:20.425041+00:00
-- url     : https://prove2.me/submissions/e681b945-b713-4c3b-9a19-fc97e87ddadd

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero



set_option autoImplicit true
open scoped Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ} {f : Ambient n → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (lastSlice f) 0 := by
  change AnalyticAt ℂ (fun w : ℂ ↦ f ((0 : Base n), w)) 0
  have haxis : AnalyticAt ℂ (fun w : ℂ ↦ ((0 : Base n), w)) 0 :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ (0 : Base n)) 0).prod analyticAt_id
  have hcomp := AnalyticAt.comp (g := f) (f := fun w : ℂ ↦ ((0 : Base n), w)) hf haxis
  simpa [Function.comp_def] using hcomp
end ClassicalComplexWPT
