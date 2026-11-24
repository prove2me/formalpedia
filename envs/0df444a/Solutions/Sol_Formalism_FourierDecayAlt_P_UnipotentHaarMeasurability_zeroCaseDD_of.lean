-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.zeroCaseDD_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:59:47.999174+00:00
-- url     : https://prove2.me/submissions/901d5cdd-156c-4de0-a2bb-476946668c89

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroOfAe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_vanishing_of_L2_equivariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 3200000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData
namespace Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
theorem _root_.solution (hBC : BeConv) (hNI : NormIdSm) (hSch : SchurH) : ZeroCaseDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inl hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inl hv) ξ).1, hDD v hv v hv]
  simp
end Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
