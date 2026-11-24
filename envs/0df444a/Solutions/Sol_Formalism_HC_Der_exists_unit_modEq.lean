-- Prove2me | solution 1 for Formalism.HC.Der.exists_unit_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:16.704141+00:00
-- url     : https://prove2.me/submissions/2f8ac5d8-5c51-4ae3-9be6-a6d91b2342c5

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
theorem _root_.solution {M N : ℕ} [NeZero N] (h : M ∣ N) (x : ℕ) (hx : x.Coprime M) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD M] := by
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective h (ZMod.unitOfCoprime x hx)
  exact ⟨u, (val_modEq_iff h u x).2 (by rw [hu, ZMod.coe_unitOfCoprime])⟩
end Formalism.HC.Der
