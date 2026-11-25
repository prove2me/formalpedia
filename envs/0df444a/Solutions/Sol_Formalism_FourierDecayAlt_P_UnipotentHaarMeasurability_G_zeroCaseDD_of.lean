-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G.zeroCaseDD_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:18.203808+00:00
-- url     : https://prove2.me/submissions/95228064-616f-412e-86e1-d74335166e64

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_VanishingOfL2Equivariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_G_vanishing_of_L2_equivariant
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
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G
namespace Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G
theorem _root_.solution (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hNI : CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm) (hSch : SchurH) : CompanionTheory.D.Upq.BesselFunctionalConstruction.ZeroCaseDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inl hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inl hv) ξ).1, hDD v hv v hv]
  simp
end Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G
