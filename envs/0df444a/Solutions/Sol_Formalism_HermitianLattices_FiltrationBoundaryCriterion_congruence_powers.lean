-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.congruence_powers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:18:47.732191+00:00
-- url     : https://prove2.me/submissions/0d8f7839-144f-4c85-8eb9-9c3eaa6aadbc

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_BehrendSets_TranslateMean
import Definitions.Def_Formalism_BehrendSets_FinalE
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfM_congruencePowers
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.FrobeniusOrbits
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion
theorem _root_.solution : CongruencePowers := PfM.congruencePowers
end Formalism.HermitianLattices.FiltrationBoundaryCriterion
