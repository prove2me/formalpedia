-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.compact_subgroup_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:07:35.674439+00:00
-- url     : https://prove2.me/submissions/86945e41-2392-4c5f-b6f5-1fbe971d4ea3

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_haarUnique
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjHaar
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
theorem _root_.solution : Formalism.FourierDecayAlt.B2.CompactConj := B2x1.compactConjFromUnique B2x1.haarUnique B2x1.conjHaar
end Formalism.FourierDecayAlt.P
