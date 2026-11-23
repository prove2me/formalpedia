-- Prove2me | solution 1 for CMEulFib.stepFib_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:17.596493+00:00
-- url     : https://prove2.me/submissions/bbf7054c-0716-4190-927d-5e9611035fbc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_FibreShapeOf
import Theorems.Thm_CMEulFib_fibreShape_of

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
open CMEulFib
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory
namespace CMEulFib
theorem _root_.solution (h : CMEul.StepConj) : CMEul.StepFib := by
  intro F E _ _ _ _ _ _ hFE v hv
  obtain ⟨σ, -, hinv, hconj, hrange, hunr⟩ := h F E hFE
  exact fibreShape_of F E hFE σ hinv hconj hrange hunr v hv
end CMEulFib
