-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.Top.modelExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:44.751231+00:00
-- url     : https://prove2.me/submissions/2823aecd-740a-44c2-bbd4-1e5859ca420f

import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WChain
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGaussK
import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_EdgeExponent
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOneK
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_modelExists_statement


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7 Formalism.InvariantFactorPaths.G7.Top
open Formalism.InvariantFactorPaths.G7
namespace Formalism.InvariantFactorPaths.G7.Top
theorem _root_.solution : ModelExists := modelExists_statement
end Formalism.InvariantFactorPaths.G7.Top
