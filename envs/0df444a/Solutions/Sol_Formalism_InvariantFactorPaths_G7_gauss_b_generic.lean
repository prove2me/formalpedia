-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.gauss_b_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:39.930021+00:00
-- url     : https://prove2.me/submissions/67aba91b-19f7-436a-a792-e38885540d0e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGaussK
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GaussBK_of
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open EGaussK DeterminantJetScaling ScaledSeriesSubstitution
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : GaussBK := GaussBK_of Top.entryB
end Formalism.InvariantFactorPaths.G7
