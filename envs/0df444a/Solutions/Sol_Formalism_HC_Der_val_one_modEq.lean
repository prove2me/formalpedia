-- Prove2me | solution 1 for Formalism.HC.Der.val_one_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:49:08.792809+00:00
-- url     : https://prove2.me/submissions/c2077a1e-3c8c-4a5b-b776-223e2626f5ed

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution (M N : ℕ) [NeZero N] (h : M ∣ N) : (((1 : (ZMod N)ˣ) : ZMod N)).val ≡ 1 [MOD M] := by
  rw [Units.val_one, ZMod.val_one_eq_one_mod]
  exact (Nat.mod_modEq 1 N).of_dvd h
end Formalism.HC.Der
