-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.principal_part_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:00:02.465873+00:00
-- url     : https://prove2.me/submissions/df6c1919-848c-4952-836e-0edb715935c5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_principalStable

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
theorem _root_.solution : PrincipalStable := PfN.principalStable
end Formalism.HermitianLattices.FiltrationBoundaryCriterion
