-- Prove2me | solution 1 for Formalism.HC.Der.exists_unit_crt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:52:05.196671+00:00
-- url     : https://prove2.me/submissions/5dd7e064-51af-4bff-b5f1-f86b16bcb705

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
namespace Formalism.HC.Der
theorem _root_.solution {A B : ℕ} [NeZero (A * B)] (hAB : A.Coprime B) (x y : ℕ) (hx : x.Coprime A) (hy : y.Coprime B) :
    ∃ u : (ZMod (A * B))ˣ, (u : ZMod (A * B)).val ≡ x [MOD A] ∧ (u : ZMod (A * B)).val ≡ y [MOD B] := by
  let z := Nat.chineseRemainder hAB x y
  have hzA : (z : ℕ) ≡ x [MOD A] := z.2.1
  have hzB : (z : ℕ) ≡ y [MOD B] := z.2.2
  have hcA : Nat.Coprime z A := by rw [Nat.Coprime, Nat.ModEq.gcd_eq hzA]; exact hx
  have hcB : Nat.Coprime z B := by rw [Nat.Coprime, Nat.ModEq.gcd_eq hzB]; exact hy
  refine ⟨ZMod.unitOfCoprime z (Nat.Coprime.mul_right hcA hcB), ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq z (A * B)).of_mul_right B).trans hzA
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq z (A * B)).of_mul_left A).trans hzB
end Formalism.HC.Der
