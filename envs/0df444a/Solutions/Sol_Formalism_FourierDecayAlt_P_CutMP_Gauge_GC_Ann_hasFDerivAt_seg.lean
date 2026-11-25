-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_seg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:59:40.791421+00:00
-- url     : https://prove2.me/submissions/501cbe78-34f0-4d65-a9bc-a4ed5371adc7

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
theorem _root_.solution (x : ℂ) (t : ℝ) :
    HasFDerivAt (fun y : ℂ => seg w₀ y t) ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ) x := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const w₀).const_smul (t : ℂ)
  have h2 := h.const_add w₀
  have hf : (fun y : ℂ => seg w₀ y t) = fun y => w₀ + ((t : ℂ) • fun x => id x - w₀) y := by
    funext y
    simp [seg, smul_eq_mul]
  rw [hf]
  exact h2
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
