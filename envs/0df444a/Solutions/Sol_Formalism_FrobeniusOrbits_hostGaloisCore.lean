-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostGaloisCore
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:55:50.583738+00:00
-- url     : https://prove2.me/submissions/9d30482e-2488-4eca-a522-40dd04ba0531

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFixed
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Galois
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostFixed ∧ HostGalois ∧ HostGalSpec := ⟨hostFixed, hostGalois, hostGalSpec⟩
end Formalism.FrobeniusOrbits
