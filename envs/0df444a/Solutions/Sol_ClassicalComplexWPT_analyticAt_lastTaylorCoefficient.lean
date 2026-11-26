-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_lastTaylorCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:32.592852+00:00
-- url     : https://prove2.me/submissions/aa0168d4-e713-4997-8b1b-afd539e3d3f2

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero


attribute [local simp] ClassicalComplexWPT.lastAxis_apply

set_option autoImplicit true
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n k : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : 0 < p.radius) :
    AnalyticAt ℂ (lastTaylorCoefficient p k) 0 := by
  let ev : ((Ambient n)[×k]→L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ Ambient n) ℂ
      (fun _ ↦ lastDirection n)
  have hc : AnalyticAt ℂ (fun z : Base n ↦ p.changeOrigin (z, 0) k) 0 :=
    (p.analyticAt_changeOrigin hp k).comp (f := fun z : Base n ↦ (z, (0 : ℂ)))
      (analyticAt_id.prod analyticAt_const :
        AnalyticAt ℂ (fun z : Base n ↦ (z, (0 : ℂ))) 0)
  have hev : AnalyticAt ℂ ev (p.changeOrigin (0, 0) k) := ev.analyticAt _
  change AnalyticAt ℂ
    (fun z : Base n ↦ p.changeOrigin (z, 0) k (fun _ ↦ lastDirection n)) 0
  simpa [ev, Function.comp_def] using
    hev.comp (f := fun z : Base n ↦ p.changeOrigin (z, 0) k) hc
end ClassicalComplexWPT
