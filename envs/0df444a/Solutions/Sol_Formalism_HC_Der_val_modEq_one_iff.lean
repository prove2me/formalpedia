-- Prove2me | solution 1 for Formalism.HC.Der.val_modEq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:10.595269+00:00
-- url     : https://prove2.me/submissions/35b901ad-a6d9-4f0f-9d3a-6eb0025082f3

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_HC_Der_val_modEq_iff

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
theorem _root_.solution {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    (u : ZMod N).val ≡ 1 [MOD M] ↔ ZMod.unitsMap h u = 1 := by
  rw [val_modEq_iff h u 1, Nat.cast_one, Units.val_eq_one]
end Formalism.HC.Der
