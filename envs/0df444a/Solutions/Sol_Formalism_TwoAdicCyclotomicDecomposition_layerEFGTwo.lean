-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layerEFGTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:16.473798+00:00
-- url     : https://prove2.me/submissions/30f1f8bb-636b-4969-ae29-99bdc64770c4

import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerReal
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerEFGTwo_of
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerGalois


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : LayerEFGTwo := layerEFGTwo_of layerGalois layerReal
end Formalism.TwoAdicCyclotomicDecomposition
