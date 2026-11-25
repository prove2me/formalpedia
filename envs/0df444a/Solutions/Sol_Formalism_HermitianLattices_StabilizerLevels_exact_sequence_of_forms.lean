-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.exact_sequence_of_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:11:52.13528+00:00
-- url     : https://prove2.me/submissions/8ec817fa-9354-4004-9942-db25fe5fa8f7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_formsExact

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
theorem _root_.solution : FormsExact := PfB.formsExact
end Formalism.HermitianLattices.StabilizerLevels
