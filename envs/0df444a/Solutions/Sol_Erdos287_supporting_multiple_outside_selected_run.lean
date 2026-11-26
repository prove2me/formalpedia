-- Prove2me | solution 1 for Erdos287.supporting_multiple_outside_selected_run
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:50:01.333181+00:00
-- url     : https://prove2.me/submissions/c7b2c468-7f89-481d-b4c4-4027b8c7132d

import Mathlib
import Theorems.Thm_Erdos287_prime_neighbor_support_for_unit_reciprocal_sums

open Finset

set_option autoImplicit false

private theorem prime_power_occurs_in_lcm (S : Finset ℕ) (p e : ℕ)
    (hp : p.Prime) (he : 1 ≤ e) (hpos : ∀ n ∈ S, 0 < n) (hdiv : p ^ e ∣ S.lcm id) :
    ∃ n ∈ S, p ^ e ∣ n := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.lcm_empty, hp.pow_dvd_iff_le_factorization Nat.one_ne_zero,
      Nat.factorization_one, Finsupp.zero_apply] at hdiv
    omega
  | @insert n S hn ih =>
    have hnp := hpos n (mem_insert_self n S)
    have hSpos : S.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr
      (fun j hj => (hpos j (mem_insert_of_mem hj)).ne')
    have hnlcm : n.lcm (S.lcm id) ≠ 0 := Nat.lcm_ne_zero hnp.ne' hSpos
    rw [Finset.lcm_insert] at hdiv
    change p ^ e ∣ n.lcm (S.lcm id) at hdiv
    rw [hp.pow_dvd_iff_le_factorization hnlcm, Nat.factorization_lcm hnp.ne' hSpos,
      Finsupp.sup_apply] at hdiv
    rcases le_max_iff.mp hdiv with h | h
    · exact ⟨n, mem_insert_self _ _, (hp.pow_dvd_iff_le_factorization hnp.ne').mpr h⟩
    · obtain ⟨j, hj, hd⟩ := ih (fun j hj => hpos j (mem_insert_of_mem hj))
        ((hp.pow_dvd_iff_le_factorization hSpos).mpr h)
      exact ⟨j, mem_insert_of_mem hj, hd⟩

/-- A prime power at least as large as a run's length must have a selected
supporting multiple outside the run. -/
theorem solution (D : Finset ℕ) (m M x w n p e : ℕ) (hm : 0 < m)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ a ∈ D, (1 : ℚ) / a = 1)
    (hcover : ∀ a, m ≤ a → a + 1 ≤ M → a ∈ D ∨ a + 1 ∈ D)
    (hn : n ∈ D) (hin : n ∈ Finset.Ico x (x + w))
    (hp : p.Prime) (he : 1 ≤ e) (hsize : w ≤ p ^ e) (hq : p ^ e ∣ n) :
    ∃ y ∈ D, y ∉ Finset.Ico x (x + w) ∧ p ^ e ∣ y := by
  have hredundant := (Erdos287.prime_neighbor_support_for_unit_reciprocal_sums
    D m M hm hD hsum hcover).1 n hn
  have hb : p ^ e ∣ (D.erase n).lcm id := hq.trans hredundant
  have hpos (y : ℕ) (hy : y ∈ D.erase n) : 0 < y :=
    hm.trans_le (mem_Icc.mp (hD (mem_of_mem_erase hy))).1
  obtain ⟨y, hy, hyd⟩ := prime_power_occurs_in_lcm (D.erase n) p e hp he hpos hb
  refine ⟨y, mem_of_mem_erase hy, ?_, hyd⟩
  intro hyin
  have hx := mem_Ico.mp hin
  have hyx := mem_Ico.mp hyin
  rcases lt_or_gt_of_ne (ne_of_mem_erase hy) with hlt | hlt
  · have hbound : p ^ e ≤ n - y := Nat.le_of_dvd (by omega) (Nat.dvd_sub hq hyd)
    omega
  · have hbound : p ^ e ≤ y - n := Nat.le_of_dvd (by omega) (Nat.dvd_sub hyd hq)
    omega

