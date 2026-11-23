-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.iwasawa_decomposition_second_model
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:21.35162+00:00
-- url     : https://prove2.me/submissions/aa970be1-3948-4681-aa8a-06eafdbba16d

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwasawaDecompositionSecondModel
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
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution : IwaHpk := fun _ _ ε _ _ => iwasawa_decomposition_unitary_group _ ε
end CompanionTheory.D.gk.admitted
