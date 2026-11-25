-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.mulEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:02:15.957908+00:00
-- url     : https://prove2.me/submissions/86207b9d-22d9-4db1-a97f-fb9c60b1377c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay

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
theorem _root_.solution (ρ : ℂ) (hρ : ρ ≠ 0) (z : ℂ) : mulEquiv ρ hρ z = ρ * z := rfl
end Formalism.FourierDecayAlt.P.PBK
