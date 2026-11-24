-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.tower_field_foundations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:38:29.126027+00:00
-- url     : https://prove2.me/submissions/5f1757f2-a531-4a87-a732-600b0d4c2072

import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerConj
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerReal
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerDecompTwo
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerInertiaTwo
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerEFGTwo
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerInertiaTame
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerFrob
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerExists
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
theorem _root_.solution :
    LayerExists ∧ LayerGalois ∧ LayerConj ∧ LayerReal ∧ LayerDecompTwo ∧ LayerInertiaTwo ∧
    LayerEFGTwo ∧ LayerInertiaTame ∧ LayerFrob :=
  ⟨layerExists, layerGalois, layerConj, layerReal, layerDecompTwo, layerInertiaTwo, layerEFGTwo,
    layerInertiaTame, layerFrob⟩
end Formalism.TwoAdicCyclotomicDecomposition
