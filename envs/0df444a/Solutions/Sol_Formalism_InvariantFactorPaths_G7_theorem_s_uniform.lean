-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.theorem_s_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:50.606351+00:00
-- url     : https://prove2.me/submissions/8f7aafe6-948f-46db-a507-97bbf46b0dca

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ThmSUniform_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_betaIsG
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_mapSimeq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_theorem_s_from_k_one


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
theorem _root_.solution : ThmSUniform :=
  ThmSUniform_of Top.betaIsG Top.theorem_s_from_k_one Top.mapSimeq
end Formalism.InvariantFactorPaths.G7
