-- Prove2me | solution 1 for Erdos287.prime_neighbor_support_for_unit_reciprocal_sums
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:52:01.79543+00:00
-- url     : https://prove2.me/submissions/ccfadf24-2115-4e89-bec8-8e857d761275

import Mathlib
import Theorems.Thm_Erdos287_reciprocal_cut_lattice

open Finset

set_option autoImplicit false

/-- An exact reciprocal sum repeats the divisibility of each denominator in
the lcm of the others. At a large prime, the spacing condition forces neighbors. -/
theorem solution (D : Finset ℕ) (lo hi : ℕ) (hlo : 0 < lo)
    (hD : D ⊆ Finset.Icc lo hi) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hcover : ∀ n, lo ≤ n → n + 1 ≤ hi → n ∈ D ∨ (n + 1) ∈ D) :
    (∀ n ∈ D, n ∣ (D.erase n).lcm id) ∧
    (∀ p : ℕ, p.Prime → hi < 2 * p →
      p ∉ D ∧ (lo ≤ p - 1 → p ≤ hi → p - 1 ∈ D) ∧
        (lo ≤ p → p + 1 ≤ hi → p + 1 ∈ D)) := by
  have hpos (n : ℕ) (hn : n ∈ D) : 0 < n := hlo.trans_le (mem_Icc.mp (hD hn)).1
  have hredundant (n : ℕ) (hn : n ∈ D) : n ∣ (D.erase n).lcm id := by
    let T := D.erase n
    let b := T.lcm id
    have hb : 0 < b := by
      have hprod : 0 < ∏ x ∈ T, x := prod_pos fun x hx => hpos x (mem_of_mem_erase hx)
      have hd : b ∣ ∏ x ∈ T, x := T.lcm_dvd_prod id
      exact Nat.pos_of_dvd_of_pos hd hprod
    have hdisj : Disjoint ({n} : Finset ℕ) T := by
      simp [T]
    have hpartition : D ⊆ {n} ∪ T := by
      intro x hx
      by_cases he : x = n
      · subst x
        exact mem_union_left _ (mem_singleton_self n)
      · exact mem_union_right _ (mem_erase.mpr ⟨he, hx⟩)
    have hcut := (Erdos287.reciprocal_cut_lattice D {n} T n b (hpos n hn) hb
      (fun x hx => by simpa using (mem_singleton.mp hx : x = n).symm ▸ dvd_rfl)
      (fun x hx => Finset.dvd_lcm hx) hdisj hpartition 1 hsum).2 rfl
    have hd := hcut.1
    rw [inter_singleton_of_mem hn, sum_singleton, one_div,
      Rat.inv_natCast_den_of_pos (hpos n hn)] at hd
    exact hd.trans (Nat.gcd_dvd_right _ _)
  refine ⟨hredundant, ?_⟩
  intro p hp hlarge
  have hpout : p ∉ D := by
    intro hpin
    have hd := hredundant p hpin
    have hprod : p ∣ ∏ n ∈ D.erase p, n := hd.trans ((D.erase p).lcm_dvd_prod id)
    obtain ⟨n, hn, hpdiv⟩ := (hp.prime.dvd_finsetProd_iff id).mp hprod
    obtain ⟨k, hk⟩ := hpdiv
    change n = p * k at hk
    have hk₀ : 0 < k := by
      have hn₀ := hpos n (mem_of_mem_erase hn)
      by_contra! h
      have hkz : k = 0 := by omega
      rw [hk, hkz, mul_zero] at hn₀
      exact (Nat.lt_irrefl 0) hn₀
    have hk₁ : k ≤ 1 := by
      by_contra! h
      apply (not_le_of_gt hlarge)
      calc
        2 * p = p * 2 := Nat.mul_comm 2 p
        _ ≤ p * k := Nat.mul_le_mul_left p (by omega)
        _ = n := hk.symm
        _ ≤ hi := (mem_Icc.mp (hD (mem_of_mem_erase hn))).2
    have hkp : k = 1 := by omega
    exact (ne_of_mem_erase hn) (by simpa [hkp] using hk)
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  exact ⟨hpout,
    fun hl hh => (hcover (p - 1) hl (hpred.trans_le hh)).resolve_right (hpred ▸ hpout),
    fun hl hh => (hcover p hl hh).resolve_left hpout⟩

