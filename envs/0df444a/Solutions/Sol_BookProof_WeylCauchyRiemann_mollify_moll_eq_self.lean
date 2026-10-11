-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.mollify_moll_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:44.181524+00:00
-- url     : https://prove2.me/submissions/d433c7ee-76e3-4828-ab25-8348c2db88b8

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.mollify_moll_eq_self
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_RadialMollifier_integral_moll_eq_self_of_analytic
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hh : DifferentiableOn ℂ h s) (hcont : Continuous h) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : closedBall z δ ⊆ s) : mollify h (moll δ) z = h z := integral_moll_eq_self_of_analytic hs hh hcont hδ hz
