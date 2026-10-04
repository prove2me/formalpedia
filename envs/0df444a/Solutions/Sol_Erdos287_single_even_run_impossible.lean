-- Prove2me | solution 1 for Erdos287.single_even_run_impossible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:19:05.548599+00:00
-- url     : https://prove2.me/submissions/a0fc3eaa-0e8a-4e72-ad6d-fd3ccc7c4ef1

import Mathlib

lemma ecba_normInv (n : ℕ) (hn : n ≠ 0) :
    padicNorm 2 ((1 : ℚ) / (n : ℚ)) = (2 : ℚ) ^ (padicValNat 2 n : ℤ) := by
  have hq : (1 : ℚ) / (n : ℚ) ≠ 0 := one_div_ne_zero (Nat.cast_ne_zero.mpr hn)
  rw [padicNorm.eq_zpow_of_nonzero hq, one_div, padicValRat.inv, padicValRat.of_nat]
  simp

lemma ecba_uniq (m t c i j : ℕ) (_hi : i < t) (hj : j < t) (hij : i < j)
    (hmax : ∀ k < t, padicValNat 2 (m + k) ≤ c)
    (hci : padicValNat 2 (m + i) = c) (hcj : padicValNat 2 (m + j) = c)
    (hm : 0 < m) : False := by
  obtain ⟨x, hx⟩ : 2 ^ c ∣ m + i := hci ▸ pow_padicValNat_dvd
  obtain ⟨y, hy⟩ : 2 ^ c ∣ m + j := hcj ▸ pow_padicValNat_dvd
  have hxodd : ¬ 2 ∣ x := by
    rintro ⟨z, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := 2) (n := m + i) (by omega)
    rw [hci, hx, pow_succ]
    exact ⟨z, by ring⟩
  have hyodd : ¬ 2 ∣ y := by
    rintro ⟨z, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := 2) (n := m + j) (by omega)
    rw [hcj, hy, pow_succ]
    exact ⟨z, by ring⟩
  have hP : 0 < 2 ^ c := by positivity
  have hxy : x < y := by
    by_contra hc
    have hc := Nat.le_of_not_lt hc
    have : 2 ^ c * y ≤ 2 ^ c * x := Nat.mul_le_mul_left _ hc
    omega
  have h1 : m + i < 2 ^ c * (x + 1) := by rw [hx, mul_add]; omega
  have h2 : 2 ^ c * (x + 1) ≤ m + j := by rw [hy]; exact Nat.mul_le_mul_left _ (by omega)
  have hk := hmax (2 ^ c * (x + 1) - m) (by omega)
  have heq : m + (2 ^ c * (x + 1) - m) = 2 ^ c * (x + 1) := by omega
  rw [heq] at hk
  have hdvd : 2 ^ (c + 1) ∣ 2 ^ c * (x + 1) := by
    obtain ⟨w, hw⟩ : 2 ∣ x + 1 := by omega
    exact ⟨w, by rw [hw, pow_succ]; ring⟩
  have := (padicValNat_dvd_iff_le (p := 2) (by positivity)).mp hdvd
  omega

theorem solution (m t : ℕ) (hm : 0 < m) (ht : 0 < t)
    (s : Finset ℕ) (g : ℕ → ℕ) (hodd : ∀ x ∈ s, ¬ 2 ∣ g x) (hg : ∀ x ∈ s, g x ≠ 0) :
    Finset.sum (Finset.range t) (fun j => (1 : ℚ) / ((2 * (m + j) : ℕ) : ℚ))
      + Finset.sum s (fun x => (1 : ℚ) / (g x : ℚ)) ≠ 1 := by
  intro h
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image (Finset.range t)
    (fun j => padicValNat 2 (m + j)) ⟨0, by simp [ht]⟩
  set c := padicValNat 2 (m + j0) with hc
  have hlt : ∀ j ∈ (Finset.range t).erase j0, padicValNat 2 (m + j) < c := by
    intro j hj
    rw [Finset.mem_erase] at hj
    obtain ⟨hne, hjr⟩ := hj
    have hle := hmax j hjr
    rcases lt_or_eq_of_le hle with hl | he
    · exact hl
    · exfalso
      have hjt := Finset.mem_range.mp hjr
      have hj0t := Finset.mem_range.mp hj0
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact ecba_uniq m t c j j0 hjt hj0t h'
          (fun k hk => hmax k (Finset.mem_range.mpr hk)) he rfl hm
      · exact ecba_uniq m t c j0 j hj0t hjt h'
          (fun k hk => hmax k (Finset.mem_range.mpr hk)) rfl he hm
  have hfnorm : ∀ j, padicNorm 2 ((1 : ℚ) / ((2 * (m + j) : ℕ) : ℚ))
      = (2 : ℚ) ^ ((padicValNat 2 (m + j) : ℤ) + 1) := by
    intro j
    rw [ecba_normInv _ (by omega), padicValNat.mul (by norm_num) (by omega)]
    simp only [padicValNat_self]
    push_cast
    ring_nf
  have hrest : padicNorm 2 (∑ j ∈ (Finset.range t).erase j0,
      (1 : ℚ) / ((2 * (m + j) : ℕ) : ℚ)) ≤ (2 : ℚ) ^ (c : ℤ) := by
    apply padicNorm.sum_le' _ (by positivity)
    intro j hj
    rw [hfnorm]
    apply zpow_le_zpow_right₀ (by norm_num)
    have := hlt j hj
    omega
  have hB : padicNorm 2 (∑ j ∈ Finset.range t, (1 : ℚ) / ((2 * (m + j) : ℕ) : ℚ))
      = (2 : ℚ) ^ ((c : ℤ) + 1) := by
    have hlt2 : (2 : ℚ) ^ (c : ℤ) < (2 : ℚ) ^ ((c : ℤ) + 1) :=
      zpow_lt_zpow_right₀ (by norm_num) (by omega)
    rw [← Finset.add_sum_erase _ _ hj0, padicNorm.add_eq_max_of_ne, hfnorm, max_eq_left]
    · linarith
    · rw [hfnorm]; linarith
  have hO : padicNorm 2 (∑ x ∈ s, (1 : ℚ) / (g x : ℚ)) ≤ 1 := by
    apply padicNorm.sum_le' _ zero_le_one
    intro x hx
    rw [ecba_normInv _ (hg x hx), padicValNat.eq_zero_of_not_dvd (hodd x hx)]
    simp
  have heq : ∑ j ∈ Finset.range t, (1 : ℚ) / ((2 * (m + j) : ℕ) : ℚ)
      = 1 - ∑ x ∈ s, (1 : ℚ) / (g x : ℚ) := by linarith
  have h3 := padicNorm.sub (p := 2) (q := 1) (r := ∑ x ∈ s, (1 : ℚ) / (g x : ℚ))
  rw [← heq, hB, padicNorm.one] at h3
  have h4 : (2 : ℚ) ^ ((c : ℤ) + 1) ≤ 1 := h3.trans (max_le le_rfl hO)
  have h5 : (1 : ℚ) < (2 : ℚ) ^ ((c : ℤ) + 1) := one_lt_zpow₀ (by norm_num) (by omega)
  linarith
