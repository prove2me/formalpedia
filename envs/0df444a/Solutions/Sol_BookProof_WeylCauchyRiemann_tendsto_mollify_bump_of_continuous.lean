-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.tendsto_mollify_bump_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:48.877448+00:00
-- url     : https://prove2.me/submissions/6a9a0adc-670c-4347-85e3-a72ed2c9d9ee

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.tendsto_mollify_bump_of_continuous
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_eq_convolution_left
import Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_rOut_tendsto
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {h : ℂ → ℂ} (hh : Continuous h) (z : ℂ) :
    Tendsto (fun n => mollify h ((bumpSeq n).normed volume) z) atTop (nhds (h z)) := by

  simpa only [mollify_eq_convolution_left] using
    ContDiffBump.convolution_tendsto_right_of_continuous (φ := bumpSeq) (l := atTop)
      bumpSeq_rOut_tendsto hh z
