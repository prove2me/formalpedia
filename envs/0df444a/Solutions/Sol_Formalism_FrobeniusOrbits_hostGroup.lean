-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:59:12.060797+00:00
-- url     : https://prove2.me/submissions/b938225e-1d32-4bc3-a95e-cf4c4dda40fa

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_ind
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_cast_eq_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_cast_eq_neg_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_card_H
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_order_le
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_hcl_pow_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Group
end Group
open Formalism.FrobeniusOrbits.Group
private lemma orderOf_hcl_u5_eq_two_pow (e : ℕ) : orderOf (hcl e (u5 (e + 2))) = 2 ^ e := by
  have hd : orderOf (hcl e (u5 (e + 2))) ∣ 2 ^ e := by
    have h0 : orderOf (hcl e (u5 (e + 2))) ∣ Nat.card (HGrp e) := by
      first
      | exact orderOf_dvd_natCard _
      | exact orderOf_dvd_card
    rwa [card_H] at h0
  obtain ⟨i, hie, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [hi]
  rcases Nat.lt_or_ge i e with hlt | hge
  · exfalso
    obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
    have hle : orderOf (hcl (j + 1) (u5 (j + 1 + 2))) ≤ 2 ^ j := by
      rw [hi]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [order_le, hcl_pow_eq_one] at hle
    have hv : ((u5 (j + 1 + 2) : (ZMod (2 ^ (j + 1 + 2)))ˣ) : ZMod (2 ^ (j + 1 + 2))) =
        ((5 : ℤ) : ZMod (2 ^ (j + 1 + 2))) := by
      first
        | (unfold u5; rw [ZMod.coe_unitOfCoprime]; norm_num)
        | (unfold u5; simp)
    have h5 : Odd (5 : ℤ) := ⟨2, by norm_num⟩
    have e3 : 3 + j = j + 1 + 2 := by omega
    rcases hle with h | h
    · have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, hv, Units.val_one, ← Int.cast_pow, cast_eq_one] at h'
      push_cast at h'
      have h8 := (ind 5 h5 3 (by norm_num) j).1 (Or.inl (by rw [e3]; exact h'))
      first
        | norm_num at h8
        | omega
    · have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, hv, Units.val_neg, Units.val_one, ← Int.cast_pow, cast_eq_neg_one] at h'
      push_cast at h'
      have h8 := (ind 5 h5 3 (by norm_num) j).1 (Or.inr (by rw [e3]; exact h'))
      first
        | norm_num at h8
        | omega
  · rw [show i = e by omega]
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Group
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostGroup := by
  unfold HostGroup
  intro e
  have hne : (-1 : ℤˣ) ≠ 1 := by
    first
      | decide
      | (intro h; have h' := congrArg Units.val h; norm_num at h')
  have hU : Nat.card ℤˣ = 2 := by
    first
      | (rw [Nat.card_eq_fintype_card]; rfl)
      | (rw [Nat.card_eq_fintype_card]; decide)
      | simp
  have hfin : Finite (HGrp e) := Nat.finite_of_card_ne_zero (by rw [card_H]; positivity)
  have h5 := orderOf_hcl_u5_eq_two_pow e
  unfold GG Psi cc sg chD G0 c0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, card_H e, h5, ?_⟩
  · rw [Nat.card_prod, Nat.card_prod, hU, card_H]
    ring
  · have hs : Function.Surjective ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.fst (ℤˣ × ℤˣ) (HGrp e))) :=
      fun b => ⟨((1, b), 1), rfl⟩
    first
      | (rw [Subgroup.index_ker, Set.range_eq_univ.2 hs, Nat.card_univ, hU])
      | (rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top, hU])
  · intro h
    rw [MonoidHom.mem_ker] at h
    exact hne h
  · rw [MonoidHom.mem_ker]
    rfl
  · apply orderOf_eq_prime
    · exact Prod.ext (Prod.ext (by simp [sq]) (by simp [sq])) (by simp [sq])
    · intro h
      exact hne (congrArg (fun x => x.1.1) h)
  · exact isCyclic_of_orderOf_eq_card _ (by rw [h5, card_H])
  · have hg : hcl e (u5 (e + 2)) ^ (2 ^ e) = 1 := by
      rw [← h5]
      exact pow_orderOf_eq_one _
    let f0 : ℤ →+ Additive (HGrp e) := zmultiplesHom (Additive (HGrp e)) (Additive.ofMul (hcl e (u5 (e + 2))))
    have hf0 : f0 ((2 ^ e : ℕ) : ℤ) = 0 := by
      show ((2 ^ e : ℕ) : ℤ) • Additive.ofMul (hcl e (u5 (e + 2))) = 0
      first
        | (rw [← ofMul_zpow, zpow_natCast, hg, ofMul_one])
        | (rw [natCast_zsmul, ← ofMul_pow, hg, ofMul_one])
        | simp [← ofMul_zpow, hg]
    let f1 : ZMod (2 ^ e) →+ Additive (HGrp e) := ZMod.lift (2 ^ e) ⟨f0, hf0⟩
    let f : Multiplicative (ZMod (2 ^ e)) →* HGrp e :=
      { toFun := fun x => Additive.toMul (f1 (Multiplicative.toAdd x))
        map_one' := by
          first
            | simp
            | rfl
        map_mul' := fun x y => by
          first
            | simp
            | (rw [toAdd_mul, map_add, toMul_add]) }
    have hf1 : f (Multiplicative.ofAdd 1) = hcl e (u5 (e + 2)) := by
      show Additive.toMul (f1 1) = hcl e (u5 (e + 2))
      have h1 : (1 : ZMod (2 ^ e)) = ((1 : ℤ) : ZMod (2 ^ e)) := by simp
      rw [h1, ZMod.lift_coe]
      show Additive.toMul ((1 : ℤ) • Additive.ofMul (hcl e (u5 (e + 2)))) = hcl e (u5 (e + 2))
      rw [one_zsmul]
      rfl
    have hsurj : Function.Surjective f := by
      intro y
      have htop : Subgroup.zpowers (hcl e (u5 (e + 2))) = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h5, card_H])
      have hy : y ∈ Subgroup.zpowers (hcl e (u5 (e + 2))) := by
        rw [htop]
        exact Subgroup.mem_top y
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine ⟨Multiplicative.ofAdd (k : ZMod (2 ^ e)), ?_⟩
      show Additive.toMul (f1 (k : ZMod (2 ^ e))) = y
      rw [ZMod.lift_coe]
      show Additive.toMul (k • Additive.ofMul (hcl e (u5 (e + 2)))) = y
      rw [← hk]
      first
        | rfl
        | simp [← ofMul_zpow]
    have hbij : Function.Bijective f := by
      haveI : NeZero (2 ^ e) := ⟨by positivity⟩
      have hc : Nat.card (Multiplicative (ZMod (2 ^ e))) ≤ Nat.card (HGrp e) := by
        change Nat.card (ZMod (2 ^ e)) ≤ Nat.card (HGrp e)
        rw [Nat.card_zmod, card_H]
      first
        | exact hsurj.bijective_of_nat_card_le hc
        | exact (Function.Surjective.bijective_of_nat_card_le hsurj hc)
    exact ⟨MulEquiv.ofBijective f hbij, hf1⟩
end Formalism.FrobeniusOrbits
