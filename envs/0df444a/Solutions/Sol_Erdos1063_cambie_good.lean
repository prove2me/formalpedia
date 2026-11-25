-- Prove2me | solution 1 for Erdos1063.cambie_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:40:57.386801+00:00
-- url     : https://prove2.me/submissions/76635d5a-45a2-41a2-80f7-23f9f0c4b3a4

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_carry_iff
public import Theorems.Thm_Erdos1063_lcm_facts

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {k i : ℕ} (hk : 3 ≤ k) (hi1 : 1 ≤ i) (hik : i < k) :
    (k * (Finset.Icc 1 (k - 1)).lcm id - i) ∣ (k * (Finset.Icc 1 (k - 1)).lcm id).choose k := by
  obtain ⟨hL0, hL2⟩ := lcm_facts hk
  set L := (Finset.Icc 1 (k - 1)).lcm id with hL
  set m := k * L with hm
  have hkm : 2 * k ≤ m := by rw [hm]; nlinarith
  have hC : m.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p e hp hpe
  have := Fact.mk hp
  have hmi0 : m - i ≠ 0 := by omega
  set c := padicValNat p (m - i) with hc
  have hec : e ≤ c := (padicValNat_dvd_iff_le hmi0).mp hpe
  suffices hcV : c ≤ padicValNat p (m.choose k) from
    (padicValNat_dvd_iff_le hC).mpr (hec.trans hcV)
  set A := Nat.log p (k - 1) with hA
  have hpA : p ^ A ≤ k - 1 := Nat.pow_log_le_self p (by omega)
  have hA1 : k - 1 < p ^ (A + 1) := Nat.lt_pow_succ_log_self hp.one_lt (k - 1)
  have hpAL : p ^ A ∣ L := by
    have : p ^ A ∈ Finset.Icc 1 (k - 1) := by
      simp only [Finset.mem_Icc]; exact ⟨Nat.one_le_pow _ _ hp.pos, hpA⟩
    exact Finset.dvd_lcm this
  have hkum := padicValNat_choose (p := p) (n := m) (k := k) (b := Nat.log p m + 1)
    (by omega) (Nat.lt_succ_self _)
  set Cs := {a ∈ Finset.Ico 1 (Nat.log p m + 1) | p ^ a ≤ k % p ^ a + (m - k) % p ^ a}
    with hCs
  rw [hkum]
  have mem_of : ∀ a, 1 ≤ a → p ^ a ≤ m → m % p ^ a < k % p ^ a → a ∈ Cs := by
    intro a ha1 hpm hcar
    rw [hCs, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨ha1, Nat.lt_succ_of_le (Nat.le_log_of_pow_le hp.one_lt hpm)⟩, ?_⟩
    exact (carry_iff (pow_pos hp.pos a) (by omega)).mpr hcar
  by_cases hcA : c ≤ A
  · -- carries at the A levels (v_p k, v_p k + A]
    set s := padicValNat p k with hs
    have hsub : Finset.Ioc s (s + A) ⊆ Cs := by
      intro a ha
      rw [Finset.mem_Ioc] at ha
      have hdm : p ^ a ∣ m := (pow_dvd_pow p ha.2).trans (by
        rw [pow_add, hm]; exact Nat.mul_dvd_mul pow_padicValNat_dvd hpAL)
      have hnk : ¬ p ^ a ∣ k := fun h => by
        have := (padicValNat_dvd_iff_le (by omega)).mp h; omega
      apply mem_of a (by omega) (Nat.le_of_dvd (by omega) hdm)
      rw [Nat.mod_eq_zero_of_dvd hdm]
      exact Nat.pos_of_ne_zero (fun h => hnk (Nat.dvd_of_mod_eq_zero h))
    have h := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at h
    omega
  · push Not at hcA
    have hdvd : p ^ (A + 1) ∣ m - i := (pow_dvd_pow p hcA).trans pow_padicValNat_dvd
    have hpk : ¬ p ∣ k := by
      intro hpk
      have hdm : p ^ (A + 1) ∣ m := by
        rw [hm, pow_succ, mul_comm (p ^ A) p]; exact Nat.mul_dvd_mul hpk hpAL
      have hdi : p ^ (A + 1) ∣ i := by
        have h' := Nat.dvd_sub hdm hdvd
        rwa [show m - (m - i) = i by omega] at h'
      have := Nat.le_of_dvd (by omega) hdi
      omega
    have hkp : k < p ^ (A + 1) := by
      rcases Nat.lt_or_ge k (p ^ (A + 1)) with h | h
      · exact h
      · exfalso
        have h' : p ^ (A + 1) = k := by omega
        exact hpk (h' ▸ dvd_pow_self p (Nat.succ_ne_zero A))
    have hsub : Finset.Icc 1 c ⊆ Cs := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have hdmi : p ^ a ∣ m - i := (pow_dvd_pow p ha.2).trans pow_padicValNat_dvd
      by_cases haA : a ≤ A
      · have hdm : p ^ a ∣ m := (pow_dvd_pow p haA).trans (hpAL.trans (dvd_mul_left L k))
        apply mem_of a ha.1 (Nat.le_of_dvd (by omega) hdm)
        rw [Nat.mod_eq_zero_of_dvd hdm]
        apply Nat.pos_of_ne_zero
        intro h
        exact hpk ((dvd_pow_self p (by omega)).trans (Nat.dvd_of_mod_eq_zero h))
      · push Not at haA
        have hka : k < p ^ a := lt_of_lt_of_le hkp (Nat.pow_le_pow_right hp.pos haA)
        have hmod : m % p ^ a = i := by
          obtain ⟨t, ht⟩ := hdmi
          have h' : m = p ^ a * t + i := by omega
          rw [h', Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        apply mem_of a ha.1 ((Nat.le_of_dvd (Nat.pos_of_ne_zero hmi0) hdmi).trans (Nat.sub_le _ _))
        rw [hmod, Nat.mod_eq_of_lt hka]
        exact hik
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    omega
end Erdos1063
