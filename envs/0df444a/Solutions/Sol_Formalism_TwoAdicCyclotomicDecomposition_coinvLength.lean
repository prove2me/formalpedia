-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.coinvLength
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:33.766485+00:00
-- url     : https://prove2.me/submissions/a991b704-8421-46f2-92fc-a2bf0ad01038

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_gcd_two_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : CoinvLength := by
  intro N u _ hu1
  set k := (u - 1).natAbs with hkdef
  have hk : k ≠ 0 := by
    rw [hkdef]; intro h; apply hu1; have := Int.natAbs_eq_zero.mp h; linarith
  have hsub : AddSubgroup.zmultiples (((u - 1 : ℤ)) : ZMod (2 ^ N)) =
      AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N)) := by
    rcases Int.natAbs_eq (u - 1) with h | h
    · rw [h]; simp [hkdef]
    · rw [h]; simp [hkdef]
  rw [hsub]
  have hN : (2 ^ N : ℕ) ≠ 0 := by positivity
  have hc := AddSubgroup.card_mul_index (AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N)))
  rw [Nat.card_zmultiples, ZMod.addOrderOf_coe _ hN, Nat.card_zmod] at hc
  have hidx : (AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N))).index = Nat.gcd (2 ^ N) k := by
    have hg : Nat.gcd (2 ^ N) k ∣ 2 ^ N := Nat.gcd_dvd_left _ _
    have hgpos : 0 < Nat.gcd (2 ^ N) k := Nat.gcd_pos_of_pos_left _ (by positivity)
    have hd : 2 ^ N / Nat.gcd (2 ^ N) k * Nat.gcd (2 ^ N) k = 2 ^ N := Nat.div_mul_cancel hg
    have hdpos : 0 < 2 ^ N / Nat.gcd (2 ^ N) k :=
      Nat.div_pos (Nat.le_of_dvd (by positivity) hg) hgpos
    exact Nat.eq_of_mul_eq_mul_left hdpos (hc.trans hd.symm)
  rw [← AddSubgroup.index, hidx, gcd_two_pow N k hk]
  rfl
end Formalism.TwoAdicCyclotomicDecomposition
