-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.uh_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:25:39.858538+00:00
-- url     : https://prove2.me/submissions/8f559d65-8988-4c48-b5dd-c4b5ec8f88eb

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
theorem _root_.solution (k r : ℕ) : PI.UpqRep.UH (PI.UpqRep.Hpk k r) = Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := rfl
end Formalism.FourierDecayAlt.P.S3dx4
