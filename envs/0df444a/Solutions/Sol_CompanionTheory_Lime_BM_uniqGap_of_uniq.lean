-- Prove2me | solution 1 for CompanionTheory.Lime.BM.uniqGap_of_uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:24.99462+00:00
-- url     : https://prove2.me/submissions/470ebfa1-62a3-43f3-b7bb-55ee1cbba220

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_BesselModels_AtFormAdmOneOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open CompanionTheory CompanionTheory.Lime CompanionTheory.Lime.BM
open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.DDSmoothness
namespace CompanionTheory.Lime.BM
theorem _root_.solution (h : PI.BesselMapUniq.BesselMapUniq) : UniqGap :=
  fun k r ε lam _ H _ _ σ z c u Wp _ _ π _ _ _ => h k r ε lam H σ z c u Wp π
end CompanionTheory.Lime.BM
