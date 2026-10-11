-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.ae_tendsto_mollify_bump
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:47.953212+00:00
-- url     : https://prove2.me/submissions/017ceda2-727c-4e3f-9afb-f962a9c4a7c7

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.ae_tendsto_mollify_bump
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_eq_convolution_left
import Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_rOut_tendsto
import Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_rOut_le
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {F : ℂ → ℂ} (hF : LocallyIntegrable F) :
    ∀ᵐ z : ℂ, Tendsto (fun n => mollify F ((bumpSeq n).normed volume) z) atTop (nhds (F z)) := by

  have := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := bumpSeq) (l := atTop) (K := 2) bumpSeq_rOut_tendsto
    (Eventually.of_forall bumpSeq_rOut_le) hF
  filter_upwards [this] with z hz
  simpa only [mollify_eq_convolution_left] using hz
