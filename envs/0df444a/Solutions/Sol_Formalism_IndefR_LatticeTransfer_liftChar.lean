-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.liftChar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:16.090748+00:00
-- url     : https://prove2.me/submissions/2786fe13-bfba-43c8-9c60-efb6f8a6faf2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open CharacterLemmas
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution : LiftChar := by
  intro K _ _ H _ _ χ
  have hint : ∀ h, IsIntegral ℤ ((χ h : Kˣ) : K) := by
    intro h
    refine IsIntegral.of_pow (orderOf_pos h) ?_
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
    exact isIntegral_one
  let φ : H →* 𝓞 K :=
    { toFun := fun h => ⟨((χ h : Kˣ) : K), hint h⟩
      map_one' := by
        apply RingOfIntegers.ext
        show ((χ 1 : Kˣ) : K) = 1
        rw [map_one, Units.val_one]
      map_mul' := fun a b => by
        apply RingOfIntegers.ext
        show ((χ (a * b) : Kˣ) : K) = ((χ a : Kˣ) : K) * ((χ b : Kˣ) : K)
        rw [map_mul, Units.val_mul] }
  exact ⟨φ.toHomUnits, fun h => rfl⟩
end Formalism.IndefR.LatticeTransfer
