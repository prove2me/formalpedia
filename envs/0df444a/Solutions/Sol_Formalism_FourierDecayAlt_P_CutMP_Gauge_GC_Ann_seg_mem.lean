-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.seg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:59.429824+00:00
-- url     : https://prove2.me/submissions/0f07f754-9d52-4522-923a-c3cc654acc75

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtTMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory intervalIntegral Metric
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) {x : ℂ} (hx : x ∈ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    seg w₀ x t ∈ S := by
  have h := hc.add_smul_sub_mem hw₀ hx ht
  simpa [seg, Complex.real_smul] using h
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
