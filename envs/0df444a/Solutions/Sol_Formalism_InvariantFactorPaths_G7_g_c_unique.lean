-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.g_c_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:05:03.843601+00:00
-- url     : https://prove2.me/submissions/0008d5a3-e6c3-48bf-846d-083723ed8f75

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GcUnique_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_dworkMv
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_frobExprG


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : GcUnique := GcUnique_of Top.dworkMv Top.frobExprG
end Formalism.InvariantFactorPaths.G7
