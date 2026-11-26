-- Prove2me | solution 1 for Erdos287.additional_omission_mass_from_prime_layers
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:21:46.940009+00:00
-- url     : https://prove2.me/submissions/9f140b4d-702d-492b-8122-df56c9938b93

import Mathlib

open Finset

set_option autoImplicit false

/-- Omitted multiples in pairwise disjoint large-prime layers contribute
reciprocal mass in addition to any previously certified omissions. -/
theorem solution (D H P : Finset ℕ) (m M Y R : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : H ⊆ Finset.Icc m M) (hHD : Disjoint H D)
    (hYM : M < Y ^ 2) (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p)
    (hsep : ∀ p ∈ P, ∀ n ∈ H, ¬ p ∣ n)
    (hR : ∀ p ∈ P, R ≤
      ((Finset.Icc ((m - 1) / p + 1) (M / p)).filter (fun c => c * p ∉ D)).card) :
    1 + (∑ n ∈ H, (1 : ℚ) / n) + ((R * P.card : ℕ) : ℚ) / M
      ≤ ∑ n ∈ Finset.Icc m M, (1 : ℚ) / n := by
  let O := Icc m M \ D
  let F (p : ℕ) := O.filter (fun n => p ∣ n)
  let A (p : ℕ) := (Icc ((m - 1) / p + 1) (M / p)).filter (fun c => c * p ∉ D)
  let W := P.biUnion F
  let w (n : ℕ) : ℚ := 1 / n
  have hM : (0 : ℚ) < M := by exact_mod_cast hm.trans_le hmM
  have hsize (p : ℕ) (hp : p ∈ P) : R ≤ (F p).card := by
    have hp0 := (hP p hp).1.pos
    have himage : (A p).image (fun c => c * p) ⊆ F p := by
      intro n hn
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hn
      obtain ⟨hcI, hcD⟩ := mem_filter.mp hc
      obtain ⟨hcl, hcu⟩ := mem_Icc.mp hcI
      have hlo : m - 1 < c * p := (Nat.div_lt_iff_lt_mul hp0).mp (Nat.lt_of_succ_le hcl)
      have hhi : c * p ≤ M := (Nat.le_div_iff_mul_le hp0).mp hcu
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, hhi⟩, hcD⟩,
        dvd_mul_left p c⟩
    have hcard : ((A p).image (fun c => c * p)).card = (A p).card :=
      card_image_of_injOn (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_right hp0 he)
    exact (hR p hp).trans (hcard ▸ card_le_card himage)
  have hpair : (↑P : Set ℕ).PairwiseDisjoint F := by
    intro p hp q hq hpq
    refine disjoint_left.mpr fun n hnp hnq => ?_
    obtain ⟨hnO, hpd⟩ := mem_filter.mp hnp
    have hnI := mem_Icc.mp (mem_sdiff.mp hnO).1
    have hCoprime := (Nat.coprime_primes (hP p hp).1 (hP q hq).1).mpr hpq
    have hprod := hCoprime.mul_dvd_of_dvd_of_dvd hpd (mem_filter.mp hnq).2
    have hnpos := hm.trans_le hnI.1
    have hle : Y ^ 2 ≤ p * q := by
      rw [pow_two]
      exact Nat.mul_le_mul (hP p hp).2 (hP q hq).2
    exact (hYM.trans_le (hle.trans (Nat.le_of_dvd hnpos hprod))).not_ge hnI.2
  have hWsub : W ⊆ O := by
    intro n hn
    obtain ⟨p, hp, hnp⟩ := mem_biUnion.mp hn
    exact (mem_filter.mp hnp).1
  have hHsub : H ⊆ O := fun n hn =>
    mem_sdiff.mpr ⟨hH hn, disjoint_left.mp hHD hn⟩
  have hHW : Disjoint H W := by
    refine disjoint_left.mpr fun n hn hnW => ?_
    obtain ⟨p, hp, hnp⟩ := mem_biUnion.mp hnW
    exact hsep p hp n hn (mem_filter.mp hnp).2
  have hone (p : ℕ) (hp : p ∈ P) : (R : ℚ) / M ≤ ∑ n ∈ F p, w n := calc
    _ ≤ ((F p).card : ℚ) / M := (div_le_div_iff_of_pos_right hM).mpr
      (by exact_mod_cast hsize p hp)
    _ = ∑ _ ∈ F p, (1 : ℚ) / M := by simp [nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      have hI := mem_Icc.mp (mem_sdiff.mp ((mem_filter.mp hn).1 : n ∈ O)).1
      apply one_div_le_one_div_of_le (by exact_mod_cast hm.trans_le hI.1)
      exact_mod_cast hI.2
  have hwlower : ((R * P.card : ℕ) : ℚ) / M ≤ ∑ n ∈ W, w n := by
    rw [show W = P.biUnion F from rfl, sum_biUnion hpair]
    calc
      _ = ∑ _ ∈ P, (R : ℚ) / M := by simp [nsmul_eq_mul, div_eq_mul_inv]; ring
      _ ≤ _ := sum_le_sum hone
  have homass : (∑ n ∈ H, w n) + (∑ n ∈ W, w n) ≤ ∑ n ∈ O, w n := by
    rw [← sum_union hHW]
    exact sum_le_sum_of_subset_of_nonneg (union_subset hHsub hWsub) (fun n _ _ => by positivity)
  have htotal := sum_sdiff (f := w) hD
  change (∑ n ∈ O, w n) + (∑ n ∈ D, (1 : ℚ) / n) = _ at htotal
  rw [hsum] at htotal
  change 1 + (∑ n ∈ H, w n) + ((R * P.card : ℕ) : ℚ) / M ≤ _
  linarith

