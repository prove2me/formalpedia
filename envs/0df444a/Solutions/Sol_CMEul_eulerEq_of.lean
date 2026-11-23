-- Prove2me | solution 1 for CMEul.eulerEq_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:51.525638+00:00
-- url     : https://prove2.me/submissions/55b0d5f8-adae-42cf-9d13-7e01f5f27a78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerEqOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEul
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory
namespace CMEul
theorem _root_.solution (hF : StepFib) (hM : StepMult) (hL : StepLocal) (hR : StepRegroup) :
    EulerEq := by
  intro F E _ _ _ _ _ _ hFE M hM3
  exact hR F E M (hM E M hM3) fun v hv => hL F E M hM3 v hv (hF F E hFE v hv)
end CMEul
