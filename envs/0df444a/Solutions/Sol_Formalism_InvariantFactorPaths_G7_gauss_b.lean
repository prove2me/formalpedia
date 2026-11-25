-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.gauss_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:05:56.705389+00:00
-- url     : https://prove2.me/submissions/79c1c78c-993d-4074-bbd9-5a567eba3fa4

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GaussB_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_entryB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open EGauss
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : GaussB := GaussB_of Top.entryB
end Formalism.InvariantFactorPaths.G7
