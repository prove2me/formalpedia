-- Prove2me | solution 1 for Formalism.HC.jacobi_pred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:38:11.814142+00:00
-- url     : https://prove2.me/submissions/2e27b7ad-6b89-4ee7-af1f-34fcd2586222

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
namespace Formalism.HC
theorem _root_.solution {p : ℕ} (hp4 : p % 4 = 3) : Nat.Coprime (p - 1) p ∧ jacobiSym ((p - 1 : ℕ) : ℤ) p = -1 := by
  constructor
  · have h2 : Nat.gcd (p - 1) p ∣ p - 1 + 1 := by
      rw [show p - 1 + 1 = p by omega]
      exact Nat.gcd_dvd_right _ _
    exact Nat.dvd_one.mp ((Nat.dvd_add_right (Nat.gcd_dvd_left _ _)).mp h2)
  · have hodd : Odd p := Nat.odd_iff.mpr (by omega)
    have hmod : ((p - 1 : ℕ) : ℤ) % (p : ℤ) = (-1 : ℤ) % (p : ℤ) := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      simp
    rw [jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hp4]
end Formalism.HC
