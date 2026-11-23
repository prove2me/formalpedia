-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.word_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:51.832832+00:00
-- url     : https://prove2.me/submissions/0b8d1fdb-534d-4a42-bd84-d418d5fc87d0

import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {R : Type*} [Ring R]
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution (E : R) : word E [] = E := rfl
end CompanionTheory.D.gk.admitted
