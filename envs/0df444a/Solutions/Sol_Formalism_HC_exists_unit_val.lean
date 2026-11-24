-- Prove2me | solution 1 for Formalism.HC.exists_unit_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:38:10.673059+00:00
-- url     : https://prove2.me/submissions/c270411c-58fe-456c-8a83-eae3b88a6722

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam

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
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
namespace Formalism.HC
theorem _root_.solution {N : ℕ} [NeZero N] {x : ℕ} (hx : Nat.Coprime x N) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD N] :=
  ⟨ZMod.unitOfCoprime x hx, by rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]; exact Nat.mod_modEq x N⟩
end Formalism.HC
