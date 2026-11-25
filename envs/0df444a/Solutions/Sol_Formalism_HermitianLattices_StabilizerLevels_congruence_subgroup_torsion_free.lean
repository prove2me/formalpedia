-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.congruence_subgroup_torsion_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:42.786191+00:00
-- url     : https://prove2.me/submissions/31c1647f-e6bf-49fe-8303-29ffb08d7b62

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_congruenceTorsion

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
theorem _root_.solution : CongruenceTorsion := PfB.congruenceTorsion
end Formalism.HermitianLattices.StabilizerLevels
