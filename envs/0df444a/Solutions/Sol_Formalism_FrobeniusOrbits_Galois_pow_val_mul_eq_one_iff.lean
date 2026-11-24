-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.pow_val_mul_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:56:06.726802+00:00
-- url     : https://prove2.me/submissions/905ac96a-18a1-4a12-8cf3-ca4aca19602b

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
    ζ ^ k.val * ζ ^ j.val = 1 ↔ k + j = 0 := by
  rw [← pow_add, hζ.pow_eq_one_iff_dvd, ← CharP.cast_eq_zero_iff (ZMod N) N, Nat.cast_add,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
end Formalism.FrobeniusOrbits.Galois
