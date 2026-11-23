-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.unitary_group_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:22.745642+00:00
-- url     : https://prove2.me/submissions/b69b501d-7c89-4bfa-ad0d-f4de6a0ead14

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinalAll
import Theorems.Thm_CompanionTheory_D_gk_admitted_admissible_of_iwasawa
import Theorems.Thm_CompanionTheory_D_gk_admitted_iwasawa_decomposition_unitary_group


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
theorem _root_.solution (n : ℕ) (ε : Fin n → Bool) : AdmUJ ε := admissible_of_iwasawa (iwasawa_decomposition_unitary_group n ε)
end CompanionTheory.D.gk.admitted
