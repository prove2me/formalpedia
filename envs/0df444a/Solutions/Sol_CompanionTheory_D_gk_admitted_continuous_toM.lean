-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.continuous_toM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:07.169806+00:00
-- url     : https://prove2.me/submissions/77966e6b-2185-477a-9c0c-0d9008640c32

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_InPCommutatorOfInK
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfFiniteRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution : Continuous (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := continuous_coeMatrix ε
end CompanionTheory.D.gk.admitted
