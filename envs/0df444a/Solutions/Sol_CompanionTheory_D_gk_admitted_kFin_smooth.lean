-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.kFin_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:41.346107+00:00
-- url     : https://prove2.me/submissions/b0fed01b-05dd-4655-b103-c31c3ebcc695

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinalAll
import Theorems.Thm_CompanionTheory_D_gk_admitted_unitary_group_admissible
import Theorems.Thm_CompanionTheory_D_gk_admitted_garding_finite_smooth_vectors
import Theorems.Thm_CompanionTheory_D_gk_admitted_smooth_of_adm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) (v : H) (hv : IsKFin ε σ v) : SmoothOnH (Jm ε) fun g => σ g v :=
  smooth_of_adm (unitary_group_admissible n ε) garding_finite_smooth_vectors hσ hirr hv
end CompanionTheory.D.gk.admitted
