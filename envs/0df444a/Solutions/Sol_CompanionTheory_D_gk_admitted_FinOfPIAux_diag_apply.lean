-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:42.831461+00:00
-- url     : https://prove2.me/submissions/1f7badf5-6042-4a61-af72-8a32570183cc

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [CompleteSpace H] [Fintype ι] [DecidableEq ι]
namespace CompanionTheory.D.gk.admitted.FinOfPIAux
theorem _root_.solution (T : H →L[ℂ] H) (z : PiLp 2 (fun _ : ι => H)) (i : ι) : diag T z i = T (z i) := rfl
end CompanionTheory.D.gk.admitted.FinOfPIAux
