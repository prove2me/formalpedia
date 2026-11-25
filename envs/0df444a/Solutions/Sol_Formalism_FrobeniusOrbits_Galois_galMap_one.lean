-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.galMap_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:36.47284+00:00
-- url     : https://prove2.me/submissions/623d1a4f-74cb-49e3-afef-6356ea4d8931

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
theorem _root_.solution (h : IsLayer (e + 2) q d ζ a b) :
    galMap h.1 a b (1 : Gal(L/ℚ)) = 1 := by
  have hs : ∀ x : L, sgn (1 : Gal(L/ℚ)) x = 1 := fun x => by
    rw [sgn.eq_1, if_pos (AlgEquiv.one_apply x)]
  rw [galMap.eq_1, map_one, hs, hs]
  rfl
end Formalism.FrobeniusOrbits.Galois
