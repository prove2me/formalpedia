-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.galMap_zeta_inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:57:20.702889+00:00
-- url     : https://prove2.me/submissions/988b6e82-9c0f-42a2-a696-36c8c246b288

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois

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
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    galMap h.1 a b (tau0 hqd h) = ((-1, 1, 1) : GalL (e + 2)) := by
  exact ((layer_galois hqd h).2.2.2.2 ((-1, 1, 1) : GalL (e + 2))).choose_spec
end Formalism.FrobeniusOrbits.Galois
