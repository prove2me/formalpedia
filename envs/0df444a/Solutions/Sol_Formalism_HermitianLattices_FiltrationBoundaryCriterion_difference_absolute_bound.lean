-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.difference_absolute_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:47:41.985008+00:00
-- url     : https://prove2.me/submissions/f981ca53-2774-4c79-ab98-f06967eadef9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_diffAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion
theorem _root_.solution : DiffAbs := PfN.diffAbs
end Formalism.HermitianLattices.FiltrationBoundaryCriterion
