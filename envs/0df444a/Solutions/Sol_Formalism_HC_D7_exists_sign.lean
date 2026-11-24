-- Prove2me | solution 1 for Formalism.HC.D7.exists_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:44.44385+00:00
-- url     : https://prove2.me/submissions/459003c6-b2db-44ed-87b5-794872702181

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HC.D7
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (s : ℤˣ) :
    ∃ b : ℕ, Nat.Coprime b p ∧ jacobiSym (b : ℤ) p = (s : ℤ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨1, Nat.coprime_one_left _, by simp [jacobiSym.one_left]⟩
  · have h1 : 1 ≤ p := hp.one_lt.le
    refine ⟨p - 1, ?_, ?_⟩
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have := Nat.le_of_dvd (by have := hp.two_le; omega) h
      omega
    · have hcast : ((p - 1 : ℕ) : ℤ) = -1 + (p : ℤ) * 1 := by push_cast [h1]; ring
      rw [hcast, jacobiSym.mod_left, Int.add_mul_emod_self_left, ← jacobiSym.mod_left (-1) p,
        jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_three_mod_four hp4]
      simp
end Formalism.HC.D7
