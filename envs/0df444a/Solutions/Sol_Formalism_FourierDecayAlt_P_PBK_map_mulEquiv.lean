-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.map_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:10.703459+00:00
-- url     : https://prove2.me/submissions/c00b7e37-b876-4ee3-b2ad-5452f38e7d08

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_map_mul_volume
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_mulEquiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (ρ : ℂ) (hρ : ρ ≠ 0) :
    Measure.map (mulEquiv ρ hρ) volume = ENNReal.ofReal ((‖ρ‖ ^ 2)⁻¹) • (volume : Measure ℂ) := by
  have h : ⇑(mulEquiv ρ hρ) = fun z => ρ * z := funext (mulEquiv_apply ρ hρ)
  rw [h]
  exact map_mul_volume ρ hρ
end Formalism.FourierDecayAlt.P.PBK
