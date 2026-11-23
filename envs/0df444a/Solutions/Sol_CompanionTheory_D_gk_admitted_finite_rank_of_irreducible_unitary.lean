-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.finite_rank_of_irreducible_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:56.823542+00:00
-- url     : https://prove2.me/submissions/09cb14c0-9779-470b-8c9f-6fed72cba339

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_stdPoly_all
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_rank_le

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
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution : FinOfPI := by
  intro G _ H _ _ _ σ hσ hirr E M h
  have hr := FinOfPIAux.rank_le E M (FinOfPIAux.stdPoly_all σ hσ hirr E M h)
  exact ⟨Module.rank_lt_aleph0_iff.mp (hr.trans_lt (Cardinal.natCast_lt_aleph0 (n := M))),
    Module.finrank_le_of_rank_le hr⟩
end CompanionTheory.D.gk.admitted
