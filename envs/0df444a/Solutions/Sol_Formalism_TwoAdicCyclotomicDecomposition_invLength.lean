-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.invLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:24.679156+00:00
-- url     : https://prove2.me/submissions/779f0492-f905-457c-9455-ba5994114efe

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_gcd_two_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : InvLength := by
  intro N u hu1
  set k := (u - 1).natAbs with hkdef
  have hk : k ≠ 0 := by
    rw [hkdef]; intro h; apply hu1; have := Int.natAbs_eq_zero.mp h; linarith
  have hN : (2 ^ N : ℕ) ≠ 0 := by positivity
  have : NeZero (2 ^ N) := ⟨hN⟩
  set c : ZMod (2 ^ N) := ((u - 1 : ℤ) : ZMod (2 ^ N)) with hc
  let f : ZMod (2 ^ N) →+ ZMod (2 ^ N) := AddMonoidHom.mulLeft c
  have hcard : Nat.card {x : ZMod (2 ^ N) // c * x = 0} = Nat.card f.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => (AddMonoidHom.mem_ker (f := f)).symm))
  have hrange : f.range = AddSubgroup.zmultiples c := by
    ext y
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(x.val : ℤ), ?_⟩
      simp only [f, AddMonoidHom.coe_mulLeft, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
      ring
    · rintro ⟨n, rfl⟩
      refine ⟨(n : ZMod (2 ^ N)), ?_⟩
      simp only [f, AddMonoidHom.coe_mulLeft, zsmul_eq_mul]
      ring
  have hord : addOrderOf c = 2 ^ N / Nat.gcd (2 ^ N) k := by
    have : c = (k : ZMod (2 ^ N)) ∨ c = -(k : ZMod (2 ^ N)) := by
      rcases Int.natAbs_eq (u - 1) with h | h
      · left; rw [hc, h]; simp [hkdef]
      · right; rw [hc, h]; simp [hkdef]
    rcases this with h | h
    · rw [h, ZMod.addOrderOf_coe _ hN]
    · rw [h, addOrderOf_neg, ZMod.addOrderOf_coe _ hN]
  have hmul := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_ker, hrange, Nat.card_zmultiples, hord, Nat.card_zmod] at hmul
  have hg : Nat.gcd (2 ^ N) k ∣ 2 ^ N := Nat.gcd_dvd_left _ _
  have hgpos : 0 < Nat.gcd (2 ^ N) k := Nat.gcd_pos_of_pos_left _ (by positivity)
  have hd : Nat.gcd (2 ^ N) k * (2 ^ N / Nat.gcd (2 ^ N) k) = 2 ^ N := Nat.mul_div_cancel' hg
  have hdpos : 0 < 2 ^ N / Nat.gcd (2 ^ N) k :=
    Nat.div_pos (Nat.le_of_dvd (by positivity) hg) hgpos
  have hker : Nat.card f.ker = Nat.gcd (2 ^ N) k :=
    Nat.eq_of_mul_eq_mul_right hdpos (hmul.trans hd.symm)
  rw [hcard, hker, gcd_two_pow N k hk]
  rfl
end Formalism.TwoAdicCyclotomicDecomposition
