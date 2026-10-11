-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.bumpSeq_rOut_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:43.144678+00:00
-- url     : https://prove2.me/submissions/85908278-f7d0-4200-852d-a48a1c7049a6

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.bumpSeq_rOut_tendsto
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : Tendsto (fun n => (bumpSeq n).rOut) atTop (nhds 0) := by

  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  simpa [bumpSeq] using tendsto_const_nhds.div_atTop (f := fun _ : ℕ => (2 : ℝ)) h
