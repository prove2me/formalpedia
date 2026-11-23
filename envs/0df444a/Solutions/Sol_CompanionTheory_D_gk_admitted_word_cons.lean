-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.word_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:20.148032+00:00
-- url     : https://prove2.me/submissions/fdc09fc9-390b-49dc-b81f-73aef55f879b

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
theorem _root_.solution (E a : R) (l : List R) : word E (a :: l) = E * a * word E l := rfl
end CompanionTheory.D.gk.admitted
