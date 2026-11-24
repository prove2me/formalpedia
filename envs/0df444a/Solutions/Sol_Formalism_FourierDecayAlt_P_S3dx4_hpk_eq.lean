-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.hpk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:27:15.497803+00:00
-- url     : https://prove2.me/submissions/6a59ad3d-7ddd-4d53-844c-b3b61fe79bc9

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution (k r : ℕ) : PI.UpqRep.Hpk k r = Formalism.QuantumDeterminants.Hpk k r := rfl
end Formalism.FourierDecayAlt.P.S3dx4
