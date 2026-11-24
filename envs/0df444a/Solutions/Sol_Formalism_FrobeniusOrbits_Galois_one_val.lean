-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.one_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:14:10.152163+00:00
-- url     : https://prove2.me/submissions/cea1668b-a5ab-4e7e-b28d-8b1c87c895a5

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_two_lt

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
theorem _root_.solution (e : ℕ) : (1 : ZMod (2 ^ (e + 2))).val = 1 := by
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (lt_trans one_lt_two (two_lt e))]
end Formalism.FrobeniusOrbits.Galois
