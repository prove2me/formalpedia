-- Prove2me | solution 1 for CMEul.eulerEq_of_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:21:48.678252+00:00
-- url     : https://prove2.me/submissions/d5472ad9-1969-4047-8a28-4fb0dc4ba473

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerEqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorsMultipliable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_Regroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorConjugate
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_Assemble
import Theorems.Thm_CMEul_eulerEq_of
import Theorems.Thm_CMEul_euler_factor_local
import Theorems.Thm_CMEul_euler_product_regroup
import Theorems.Thm_euler_factors_multipliable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CMEul
namespace CMEul
theorem _root_.solution (hF : StepFib) : Formalism.L2.SG.MassRatio.EulerEq :=
  eulerEq_of hF _root_.euler_factors_multipliable euler_factor_local euler_product_regroup
end CMEul
