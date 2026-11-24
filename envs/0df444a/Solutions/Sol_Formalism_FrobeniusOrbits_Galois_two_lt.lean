-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.two_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:56:09.490702+00:00
-- url     : https://prove2.me/submissions/03415745-fce0-4729-bdbe-329e78d8ecf4

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
theorem _root_.solution (e : ℕ) : 2 < 2 ^ (e + 2) := by
  have h4 : 2 ^ 2 ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (e + 2) := h4
end Formalism.FrobeniusOrbits.Galois
