-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.pow_val_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:00:14.468417+00:00
-- url     : https://prove2.me/submissions/d89bdd4f-2bcf-4d68-832a-09f6b7475cbf

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
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (hζ : IsPrimitiveRoot ζ N) (k j : ZMod N) :
    ζ ^ k.val = ζ ^ j.val ↔ k = j := by
  constructor
  · intro hkj
    exact ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt k) (ZMod.val_lt j) hkj)
  · rintro rfl
    rfl
end Formalism.FrobeniusOrbits.Galois
