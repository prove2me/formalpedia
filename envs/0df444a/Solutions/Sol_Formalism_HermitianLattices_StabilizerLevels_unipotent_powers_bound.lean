-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.unipotent_powers_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:33.705723+00:00
-- url     : https://prove2.me/submissions/693a2e5a-9154-4ff6-9bba-b7e249096cf1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_unipotentPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
namespace Formalism.HermitianLattices.StabilizerLevels
theorem _root_.solution : UnipotentPowers := PfB.unipotentPowers
end Formalism.HermitianLattices.StabilizerLevels
