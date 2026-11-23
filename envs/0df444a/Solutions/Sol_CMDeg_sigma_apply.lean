-- Prove2me | solution 1 for CMDeg.sigma_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:33.971358+00:00
-- url     : https://prove2.me/submissions/e3986efa-decc-4bea-bd6d-d1f4e264bd65

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open CMDeg
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
namespace CMDeg
theorem _root_.solution (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (a : E) :
    sigma hfix a = star a := rfl
end CMDeg
