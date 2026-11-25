-- Prove2me | solution 1 for Erdos1063.valuation_bound_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:37:01.001547+00:00
-- url     : https://prove2.me/submissions/0f341c7a-305d-412e-a2b5-c2f282d321ad

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_carry_iff

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {n k p i0 : ℕ} (hp : p.Prime) (hkn : 2 * k ≤ n) (hpk : p ∣ k)
    (hk : 2 ≤ k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) :
    padicValNat p (n.choose k) + padicValNat p k ≤ padicValNat p (n - i0) ∧
      padicValNat p k + Nat.log p (k - 1) ≤ padicValNat p (n - i0) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hC : n.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  set V := padicValNat p (n.choose k) with hV
  set a := padicValNat p k with ha
  set L' := Nat.log p (k - 1) with hL'
  -- good elements have valuation at most V
  have hle : ∀ i < k, i ≠ i0 → padicValNat p (n - i) ≤ V := by
    intro i hi hne
    have : p ^ padicValNat p (n - i) ∣ n.choose k :=
      (pow_padicValNat_dvd).trans (hgood i hi hne)
    exact (padicValNat_dvd_iff_le hC).mp this
  have hdvd_r : ∀ e, p ^ e ∣ n - n % p ^ e := fun e => Nat.dvd_sub_mod n
  -- two multiples of p^e in the block force e ≤ V
  have two : ∀ e, n % p ^ e + p ^ e < k → e ≤ V := by
    intro e he
    have d1 := hdvd_r e
    have d2 : p ^ e ∣ n - (n % p ^ e + p ^ e) := by
      have : n - (n % p ^ e + p ^ e) = (n - n % p ^ e) - p ^ e := by omega
      rw [this]; exact Nat.dvd_sub d1 (dvd_refl _)
    by_cases h : n % p ^ e = i0
    · have hne : n % p ^ e + p ^ e ≠ i0 := by
        have := pow_pos hp.pos e; omega
      have hpos : n - (n % p ^ e + p ^ e) ≠ 0 := by omega
      exact ((padicValNat_dvd_iff_le hpos).mp d2).trans (hle _ he hne)
    · have hpos : n - n % p ^ e ≠ 0 := by omega
      exact ((padicValNat_dvd_iff_le hpos).mp d1).trans (hle _ (by omega) h)
  -- the maximal valuation in the block
  obtain ⟨istar, histar, hmax⟩ := Finset.exists_max_image (Finset.range k)
    (fun i => padicValNat p (n - i)) ⟨0, by simp; omega⟩
  set M := padicValNat p (n - istar) with hM
  have hmaxM : ∀ i < k, padicValNat p (n - i) ≤ M := fun i hi => hmax i (by simpa using hi)
  have reach : ∀ e, n % p ^ e < k → e ≤ M := by
    intro e he
    have hpos : n - n % p ^ e ≠ 0 := by omega
    exact ((padicValNat_dvd_iff_le hpos).mp (hdvd_r e)).trans (hmaxM _ he)
  have hpow_le : ∀ e, p ^ e ≤ k → e ≤ M := fun e he =>
    reach e (lt_of_lt_of_le (Nat.mod_lt _ (pow_pos hp.pos e)) he)
  -- Kummer
  have hkum := padicValNat_choose (p := p) (n := n) (k := k) (b := Nat.log p n + 1)
    (by omega) (Nat.lt_succ_self _)
  set Cset := {i ∈ Finset.Ico 1 (Nat.log p n + 1) | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}
    with hCset
  have hVc : V = Cset.card := hkum
  have carry_mem : ∀ e ∈ Cset, n % p ^ e < k % p ^ e := by
    intro e he
    rw [hCset, Finset.mem_filter] at he
    exact (carry_iff (pow_pos hp.pos e) (by omega)).mp he.2
  have hapos : 1 ≤ a := one_le_padicValNat_of_dvd (by omega) hpk
  have hpa : p ^ a ∣ k := pow_padicValNat_dvd
  have hsub1 : Cset ⊆ Finset.Ioc a M := by
    intro e he
    have hc := carry_mem e he
    rw [Finset.mem_Ioc]
    constructor
    · by_contra hle'
      push Not at hle'
      have : p ^ e ∣ k := (pow_dvd_pow p hle').trans hpa
      rw [Nat.mod_eq_zero_of_dvd this] at hc
      exact Nat.not_lt_zero _ hc
    · exact reach e (lt_of_lt_of_le hc (Nat.mod_le _ _))
  have hVle : V ≤ M - a := by
    rw [hVc]
    have := Finset.card_le_card hsub1
    simpa using this
  have haM : a ≤ M := hpow_le a (Nat.le_of_dvd (by omega) hpa)
  have hL'k : p ^ L' ≤ k - 1 := Nat.pow_log_le_self p (by omega)
  have hL'M : L' ≤ M := hpow_le L' (by omega)
  -- the maximum is attained only at i0
  have hstar : istar = i0 := by
    by_contra hne
    have := hle istar (by simpa using histar) hne
    omega
  have hM0 : padicValNat p (n - i0) = M := by rw [hM, hstar]
  rw [hM0]
  refine ⟨by omega, ?_⟩
  by_cases hcase : L' ≤ V
  · omega
  · push Not at hcase
    have haL : a ≤ L' := by
      by_contra h'
      push Not at h'
      have h1 : p ^ (L' + 1) ≤ k :=
        (Nat.pow_le_pow_right hp.pos h').trans (Nat.le_of_dvd (by omega) hpa)
      have h2 : 2 * p ^ L' ≤ p ^ (L' + 1) := by
        rw [pow_succ]; nlinarith [pow_pos hp.pos L']
      have := two L' (by have := Nat.mod_lt n (pow_pos hp.pos L'); omega)
      omega
    have haV : a ≤ V := by
      have h1 : p ^ a ≤ k - 1 := (Nat.pow_le_pow_right hp.pos haL).trans hL'k
      obtain ⟨m, hm⟩ := hpa
      have hm2 : 2 ≤ m := by
        by_contra h'
        push Not at h'
        interval_cases m <;> simp at hm <;> omega
      have h3 : 2 * p ^ a ≤ k := by rw [hm]; nlinarith [pow_pos hp.pos a]
      exact two a (by have := Nat.mod_lt n (pow_pos hp.pos a); omega)
    have hsub2 : Cset ⊆ Finset.Ioc a M \ Finset.Ioc V L' := by
      intro e he
      rw [Finset.mem_sdiff]
      refine ⟨hsub1 he, ?_⟩
      intro he2
      rw [Finset.mem_Ioc] at he2
      have hc := carry_mem e he
      have hqk : p ^ e ≤ k - 1 := (Nat.pow_le_pow_right hp.pos he2.2).trans hL'k
      have hmodk : k % p ^ e + p ^ e ≤ k := by
        have h5 := Nat.mod_add_div k (p ^ e)
        have hdiv : 1 ≤ k / p ^ e := (Nat.one_le_div_iff (pow_pos hp.pos e)).mpr (by omega)
        have h6 : p ^ e ≤ p ^ e * (k / p ^ e) := by
          simpa using Nat.mul_le_mul_left (p ^ e) hdiv
        omega
      have := two e (by omega)
      omega
    have hsub3 : Finset.Ioc V L' ⊆ Finset.Ioc a M := by
      intro e he; rw [Finset.mem_Ioc] at he ⊢; omega
    have hcard := Finset.card_le_card hsub2
    rw [Finset.card_sdiff_of_subset hsub3] at hcard
    simp only [Nat.card_Ioc] at hcard
    rw [← hVc] at hcard
    omega
end Erdos1063
