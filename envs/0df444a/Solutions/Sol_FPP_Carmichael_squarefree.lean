-- Prove2me | solution 1 for FPP.Carmichael.squarefree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:04.417231+00:00
-- url     : https://prove2.me/submissions/e7f0890b-52a8-4a0a-bbe0-8bd0231a427d

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable
import Theorems.Thm_FPP_fpp_unit_iff
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_ZMod_add_mul_prime_pow_pow
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
import Theorems.Thm_ZMod_unitsMap_neg
attribute [local simp] P2M_ZMod_fst_chineseRemainder__e38dff19d888
attribute [local simp] P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder
attribute [local simp] ZMod.unitsMap_neg



set_option autoImplicit false
open Nat
open FPP
open FPP.Carmichael
variable {n : ℕ}
namespace FPP.Carmichael
theorem _root_.solution [hn : NeZero n] (hc : Carmichael n) :
    Squarefree n := by
  rw [squarefree_iff_prime_squarefree]
  simp_rw [Carmichael, fpp_unit_iff] at hc
  contrapose! hc
  obtain ⟨p, pp, m, rfl⟩ := hc
  have : Fact p.Prime := ⟨pp⟩
  have mpos : 0 < m := pos_iff_ne_zero.mpr ((mul_ne_zero_iff.mp hn.out).2)
  let s := padicValNat p m
  obtain ⟨k, hk : m = p ^ s * k⟩ := pow_padicValNat_dvd
  have cop : (p ^ (s + 2)).Coprime k := by
    apply Coprime.pow_left
    refine (coprime_or_dvd_of_prime pp k).elim id fun h ↦ absurd h ?_
    rw [← mul_dvd_mul_iff_left (pow_ne_zero s pp.ne_zero), ← Nat.pow_succ, ← hk]
    exact pow_succ_padicValNat_not_dvd mpos.ne'
  let one_p :=
    ZMod.unitOfCoprime (1 + p) ((coprime_add_self_left.mpr (coprime_one_left p)).pow_right (s + 2))
  let a := (ZMod.chineseRemainderₓ cop).symm (one_p, 1)
  rw [hk, ← mul_assoc, ← pow_two, ← pow_add, add_comm]
  use a
  intro ha
  apply_fun ZMod.unitsMap (dvd_mul_right _ k) at ha
  rw [map_pow, ZMod.unitsMap_chineseRemainderₓ_symm] at ha
  apply_fun ZMod.unitsMap ((pow_dvd_pow_iff_le_right pp.one_lt).mpr le_add_self) at ha
  have pos : 0 < p ^ (s + 2) * k - 1 := Nat.sub_pos_of_lt <| by
    rw [add_comm, pow_add, mul_assoc, Nat.one_lt_mul_iff]
    use sq_pos_of_pos pp.pos, hk ▸ mpos
    left
    exact Nat.one_lt_pow two_ne_zero pp.one_lt
  have : (1 + p : ZMod (p ^ 2)) ^ (p ^ (s + 2) * k - 1) = 1 + p * ↑(p ^ (s + 2) * k - 1) := by
    simpa using ZMod.add_mul_prime_pow_pow 1 1 one_pos pos
  rw [map_pow, map_one, map_one, ZMod.unitsMap_def, Units.ext_iff, Units.val_pow_eq_pow_val,
    Units.coe_map, ZMod.coe_unitOfCoprime, cast_add, cast_one, MonoidHom.coe_coe, map_add, map_one,
    map_natCast, Units.val_one, this, cast_sub (lt_of_lt_pred pos), cast_mul, pow_add p s 2,
    cast_mul, ZMod.natCast_self, mul_zero, zero_mul, zero_sub, cast_one, mul_neg_one,
    add_eq_left, neg_eq_zero, ZMod.natCast_eq_zero_iff] at ha
  suffices 2 ≤ 1 by norm_num at this
  apply (pow_dvd_pow_iff_le_right pp.one_lt).mp
  rwa [pow_one]
end FPP.Carmichael
