-- Prove2me | solution 1 for Formalism.L2.SG.MassRatio.mass_ratio_euler_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:47.040583+00:00
-- url     : https://prove2.me/submissions/6708e377-2d5a-4fcc-848d-e29d40280f40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_FibreShapeOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CMEulerEq
import Theorems.Thm_CMEulFib_stepFib_of
import Theorems.Thm_CMEul_eulerEq_of_fib
import Theorems.Thm_CMEul_euler_factor_conjugate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.L2.SG.MassRatio
theorem _root_.solution : Formalism.L2.SG.MassRatio.EulerEq :=
  CMEul.eulerEq_of_fib (CMEulFib.stepFib_of CMEul.euler_factor_conjugate)
end Formalism.L2.SG.MassRatio
