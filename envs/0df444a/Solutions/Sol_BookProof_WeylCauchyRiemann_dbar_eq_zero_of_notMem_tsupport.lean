-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.dbar_eq_zero_of_notMem_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:39:42.943045+00:00
-- url     : https://prove2.me/submissions/2196160f-c6d3-4a74-829c-1b2405fe2cf3

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.dbar_eq_zero_of_notMem_tsupport
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {φ : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport φ) :
    dbar φ z = 0 := by

  have h0 : φ =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [(isOpen_compl_iff.2 (isClosed_tsupport φ)).mem_nhds hz] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  simp only [dbar, h0.fderiv_eq]
  simp
