-- Prove2me | solution 1 for FPP.Carmichael.sub_one_dvd_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:10:06.890367+00:00
-- url     : https://prove2.me/submissions/9342663a-6ae1-4c98-81fe-0e7d742b0e2b

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable
import Theorems.Thm_FPP_fpp_unit_iff
import Theorems.Thm_FPP_Carmichael_squarefree
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158



set_option autoImplicit false
open Nat
open FPP
open FPP.Carmichael
variable {n : ℕ}
namespace FPP.Carmichael
theorem _root_.solution {p : ℕ} [NeZero n] [Fact p.Prime] (hc : Carmichael n)
    (hp : p ∣ n) : p - 1 ∣ n - 1 := by
  apply ZMod.card p ▸ (FiniteField.forall_pow_eq_one_iff (ZMod p) (n - 1)).mp
  obtain ⟨k, rfl⟩ := hp
  have cop := coprime_of_squarefree_mul hc.squarefree
  intro b
  let a := (ZMod.chineseRemainderₓ cop).symm (b, 1)
  have ha : a ^ (p * k - 1) = 1 := fpp_unit_iff.mp (hc a)
  apply_fun ZMod.unitsMap (dvd_mul_right _ k) at ha
  rwa [map_pow, map_one, ZMod.unitsMap_chineseRemainderₓ_symm] at ha
end FPP.Carmichael
