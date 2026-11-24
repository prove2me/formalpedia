-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.mem_hostE_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:42:31.809815+00:00
-- url     : https://prove2.me/submissions/d3097b4b-83ff-416a-93c4-59ef84b1000b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_mem_fixedField_zpowers
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hostE_eq_fixedField

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
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (x : L) :
    x ∈ hostE ζ a b ↔ tau0 hqd h x = x := by
  rw [hostE_eq_fixedField hqd h, mem_fixedField_zpowers]
end Formalism.FrobeniusOrbits.Galois
