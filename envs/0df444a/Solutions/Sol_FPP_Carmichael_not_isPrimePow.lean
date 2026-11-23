-- Prove2me | solution 1 for FPP.Carmichael.not_isPrimePow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:34.238433+00:00
-- url     : https://prove2.me/submissions/26229b39-ae0e-4f6d-ae5a-ec6f21a6b657

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable
import Theorems.Thm_FPP_Carmichael_card_primeFactors
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
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
theorem _root_.solution [Fact (1 < n)] (hc : Carmichael n) (hnp : ¬n.Prime) :
    ¬IsPrimePow n := by
  rintro ⟨p, k, pp, hk, rfl⟩
  have h := hc.card_primeFactors hnp
  simp [primeFactors_prime_pow hk.ne' pp.nat_prime] at h
end FPP.Carmichael
