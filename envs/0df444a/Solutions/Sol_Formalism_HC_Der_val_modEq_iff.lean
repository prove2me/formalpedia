-- Prove2me | solution 1 for Formalism.HC.Der.val_modEq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:30:32.895791+00:00
-- url     : https://prove2.me/submissions/bcce4b90-8071-4e28-a26e-39cf4a49aa5d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem

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
namespace Formalism.HC.Der
theorem _root_.solution {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) (x : ℕ) :
    (u : ZMod N).val ≡ x [MOD M] ↔ ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = (x : ZMod M) := by
  rw [show ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = ((u : ZMod N).val : ZMod M) from
    ZMod.cast_eq_val _, ZMod.natCast_eq_natCast_iff]
end Formalism.HC.Der
