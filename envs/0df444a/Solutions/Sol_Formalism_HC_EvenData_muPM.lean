-- Prove2me | solution 1 for Formalism.HC.EvenData.muPM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:51:57.75895+00:00
-- url     : https://prove2.me/submissions/d19d3038-9325-4f95-9c4e-263358d2680a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Theorems.Thm_Formalism_HC_EvenData_art_ch_one
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_CharData_muPM
import Theorems.Thm_Formalism_HC_D7_cop_qd
import Theorems.Thm_Formalism_HC_D7_d4
import Theorems.Thm_Formalism_HC_D7_q4
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_unitsMap_neg_one
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
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
attribute [instance] EvenData.grp
open Formalism.HC.EvenData
variable (D : EvenData)
variable {q d : ℕ} (hH : HostHyp q d)
variable (hc : Nat.Coprime D.m (q * d))
variable (he : 2 ≤ D.e) (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ D.m → jacobiSym (-(d : ℤ)) l = 1)
namespace Formalism.HC.EvenData
theorem _root_.solution (hq : q ≠ 3) : (D.host hH hc he hs).MuPM := by
  have := D.neZeroN hH
  refine (D.charData hH hc he hs).muPM fun k (hk : k ∣ D.m * q * d)
    (h : ∀ u : (ZMod (D.m * q * d))ˣ, D.art hH u = 1 → (u : ZMod (D.m * q * d)).val ≡ 1 [MOD k]) => ?_
  have hq2 := D7.q4 hH
  have hd2 := D7.d4 hH
  have c4 : ∀ p : ℕ, p % 4 = 3 → Nat.Coprime 4 p := fun p hp =>
    Nat.Coprime.pow_left 2 ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr (by omega)))
  have j4 : ∀ p : ℕ, p % 4 = 3 → jacobiSym ((4 : ℕ) : ℤ) p = 1 := fun p hp => by
    have h2 : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr (Nat.odd_iff.mpr (by omega))
    exact jacobiSym.sq_one' (a := 2) h2
  have n4 : ∀ p : ℕ, p.Prime → p ≠ 3 → ¬ 4 ≡ 1 [MOD p] := fun p hp h3 h4 =>
    h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp ((Nat.modEq_iff_dvd' (by norm_num)).mp h4.symm))
  have ex := exists_unit_three hc.coprime_mul_right_right hc.coprime_mul_left_right (D7.cop_qd hH)
  have kq : Nat.Coprime k q := by
    refine ((Nat.Prime.coprime_iff_not_dvd hH.1).mpr fun hqk => ?_).symm
    obtain ⟨u, h1, h2, h3⟩ := ex 1 4 1 (Nat.coprime_one_left _) (c4 q hq2) (Nat.coprime_one_left _)
    have h4 := h u (Prod.ext (Prod.ext (D.art_ps_one hH u h2 (j4 q hq2)) (D.art_ch_one hH u h3 (by simp)))
      (D.art_snd_one hH u h1))
    exact n4 q hH.1 hq (h2.symm.trans (h4.of_dvd hqk))
  have kd : Nat.Coprime k d := by
    refine ((Nat.Prime.coprime_iff_not_dvd hH.2.1).mpr fun hqk => ?_).symm
    obtain ⟨u, h1, h2, h3⟩ := ex 1 1 4 (Nat.coprime_one_left _) (Nat.coprime_one_left _) (c4 d hd2)
    have h4 := h u (Prod.ext (Prod.ext (D.art_ps_one hH u h2 (by simp)) (D.art_ch_one hH u h3 (j4 d hd2)))
      (D.art_snd_one hH u h1))
    exact n4 d hH.2.1 (by have := hH.2.2.2.1; omega) (h3.symm.trans (h4.of_dvd hqk))
  have km : k ∣ D.m := kq.dvd_of_dvd_mul_right (kd.dvd_of_dvd_mul_right hk)
  obtain ⟨u, h1, h2, h3⟩ := ex ((-1 : (ZMod D.m)ˣ) : ZMod D.m).val 1 1 (ZMod.val_coe_unit_coprime _)
    (Nat.coprime_one_left _) (Nat.coprime_one_left _)
  have h4 := h u (Prod.ext (Prod.ext (D.art_ps_one hH u h2 (by simp)) (D.art_ch_one hH u h3 (by simp))) (by
    rw [art_snd, (unitsMap_eq_iff _ u _).mpr h1]
    exact (D.toA_eq_one_iff _).mpr D.eta_neg_one))
  have h5 := (unitsMap_eq_one_iff km (-1)).mpr ((h1.of_dvd km).symm.trans h4)
  rw [D7.unitsMap_neg_one, Units.ext_iff, Units.val_neg, Units.val_one] at h5
  refine (ZMod.natCast_eq_zero_iff 2 k).mp ?_
  push_cast
  linear_combination -h5
end Formalism.HC.EvenData
