-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layerConj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:31.694207+00:00
-- url     : https://prove2.me/submissions/9588770e-8bf2-46e1-ba72-94655b358e78

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_conj_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open UnitConjugation
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (_hG : LayerGalois) : LayerConj := by
  intro n q d _ hqd L _ _ ζ a b h φ σ
  exact conj_iff hqd.1.pos hqd.2.1.pos h φ σ
end Formalism.TwoAdicCyclotomicDecomposition
