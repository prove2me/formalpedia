-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:01:48.094822+00:00
-- url     : https://prove2.me/submissions/c4603645-941e-4dae-8ec1-205cc2670cfd

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinalAll
import Theorems.Thm_CompanionTheory_D_gk_admitted_kFin_smooth

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
    (hirr : IsIrredOn (UJset ε) σ) (v : H) (hv : IsKFin ε σ v) :
    v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ :=
  kFin_smooth n ε H σ hσ hirr v hv
end CompanionTheory.D.gk.admitted
