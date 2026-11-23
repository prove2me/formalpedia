-- Prove2me | solution 1 for CMDeg.sigma_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:44.778858+00:00
-- url     : https://prove2.me/submissions/272417a9-209e-418a-9976-103a97730222

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Theorems.Thm_CMDeg_sigma_apply

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
theorem _root_.solution (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) :
    sigma hfix ^ 2 = 1 := by
  ext a
  simp [pow_two, AlgEquiv.mul_apply, sigma_apply]
end CMDeg
