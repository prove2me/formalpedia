-- Prove2me | solution 1 for FPP.Carmichael.card_primeFactors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:11:34.94301+00:00
-- url     : https://prove2.me/submissions/714e0107-2469-4f89-b4c8-3d5559973f1c

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable
import Theorems.Thm_FPP_Carmichael_squarefree
import Theorems.Thm_FPP_Carmichael_sub_one_dvd_sub_one
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
theorem _root_.solution [hn : Fact (1 < n)] (hc : Carmichael n) (hnp : ¬n.Prime) :
    3 ≤ n.primeFactors.card := by
  by_contra hf
  interval_cases h : n.primeFactors.card
  · have := hn.out
    simp at h
    omega
  · apply hnp
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
    convert prime_of_mem_primeFactors (hp ▸ Finset.mem_singleton_self p)
    simpa [hp] using prod_primeFactors_of_squarefree hc.squarefree |>.symm
  · obtain ⟨p, q, hne, hpq⟩ := Finset.card_eq_two.mp h
    have pp : p.Prime := prime_of_mem_primeFactors (by rw [hpq]; simp)
    have pq : q.Prime := prime_of_mem_primeFactors (by rw [hpq]; simp)
    replace hpq := hpq ▸ prod_primeFactors_of_squarefree hc.squarefree |>.symm
    rw [Finset.prod_insert (Finset.notMem_singleton.mpr hne), Finset.prod_singleton] at hpq
    wlog hlt : p < q
    · apply this hc hnp h (by decide) q p hne.symm pq pp (by rwa [mul_comm] at hpq)
      exact lt_of_le_of_ne (not_lt.mp hlt) fun heq ↦
        squarefree_iff_prime_squarefree.mp hc.squarefree p pp <|
          by nth_rw 2 [← heq]; rw [hpq]
    have hdvd : q - 1 ∣ n - 1 :=
      have : Fact q.Prime := ⟨pq⟩
      hc.sub_one_dvd_sub_one (hpq ▸ dvd_mul_left q p)
    have : p * q - 1 = (p - 1) * q + (q - 1) := by
      have : q ≤ p * q := Nat.le_mul_of_pos_left q pp.pos
      rw [tsub_mul]
      omega
    rw [hpq, this, Nat.dvd_add_self_right] at hdvd
    have cop : (q - 1).Coprime q := (coprime_self_sub_left pq.pos).mpr (coprime_one_left q)
    have := succ_le_succ (le_of_dvd (lt_pred_of_succ_lt pp.one_lt) (cop.dvd_of_dvd_mul_right hdvd))
    rw [succ_pred pp.ne_zero, q.sub_one, succ_pred pq.ne_zero] at this
    exact this.not_gt hlt
end FPP.Carmichael
