-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.compact_conjugation_of_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:39:23.780137+00:00
-- url     : https://prove2.me/submissions/fc1dbb08-baff-4219-82e1-67fa7a4a8e71

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_compactConjFromUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.CompactConjFromUnique := B2x1.compactConjFromUnique
end Formalism.FourierDecayAlt.P
