-- Prove2me | solution 1 for Erdos287.exceptional_endpoint_carries
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:06:48.201507+00:00
-- url     : https://prove2.me/submissions/9edccd8c-d4cc-453a-baf9-76f4b46f3c5c

import Mathlib
import Theorems.Thm_Erdos287_cofactor_cut_congruence
import Theorems.Thm_Erdos287_dense_prime_power_endpoint_restrictions

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem cofactor_mem_interval (D : Finset ℕ) (m M r a b : ℕ)
    (hD : D ⊆ Finset.Icc m M) (hl : (a - 1) * r < m) (hu : M < (b + 1) * r)
    (c : ℕ) (hc : c * r ∈ D) : c ∈ Finset.Icc a b := by
  obtain ⟨hcl, hcu⟩ := mem_Icc.mp (hD hc)
  have hal : a - 1 < c := Nat.lt_of_mul_lt_mul_right (hl.trans_le hcl)
  have hbu : c < b + 1 := Nat.lt_of_mul_lt_mul_right (hcu.trans_lt hu)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

private theorem sum_of_cofactors (D : Finset ℕ) (r L a b : ℕ) (hr : 0 < r)
    (hb : ∀ c, c * r ∈ D → c ∈ Finset.Icc a b) :
    (∑ n ∈ D.filter (fun n => r ∣ n), L / (n / r)) =
      ∑ c ∈ (Finset.Icc a b).filter (fun c => c * r ∈ D), L / c := by
  let C := (Finset.Icc a b).filter (fun c => c * r ∈ D)
  have hmap : C.image (fun c => c * r) = D.filter (fun n => r ∣ n) := by
    ext n
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨(mem_filter.mp hc).2, dvd_mul_left r c⟩
    · rintro ⟨hn, ⟨c, hc⟩⟩
      have he : c * r = n := by simpa [mul_comm] using hc.symm
      have hd : c * r ∈ D := he ▸ hn
      exact ⟨c, mem_filter.mpr ⟨hb c hd, hd⟩, he⟩
  rw [← hmap, sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_right hr h)]
  exact sum_congr rfl fun c _ => by rw [Nat.mul_div_cancel _ hr]

/-- The next lower valuation layer gives additional forced selections and
omissions at both exceptional endpoint forms. -/
theorem solution (D : Finset ℕ) (m M j : ℕ) (hm : 0 < m) (hj : 1 ≤ j)
    (hD : D ⊆ Finset.Icc m M) (hmD : m ∈ D) (hMD : M ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) (hratio : M < 3 * m) :
    (M = 6 * 3 ^ j → 4 * 3 ^ j ∈ D ∧ 5 * 3 ^ j ∉ D) ∧
    (M = 15 * 5 ^ j →
      let T := (Finset.Icc 6 14).filter (fun c => c ≠ 10 ∧ c * 5 ^ j ∉ D)
      (∑ c ∈ T, 72072 / c) % 5 = 2 ∧ (∀ c, T = {c} → c = 6 ∨ c = 11)) := by
  classical
  have hpos (n : ℕ) (hn : n ∈ D) : 0 < n := hm.trans_le (mem_Icc.mp (hD hn)).1
  constructor
  · intro hM
    let r := 3 ^ j
    change M = 6 * r at hM
    have hr : 0 < r := pow_pos (by decide) _
    have hpow : 3 ^ (j + 1) = 3 * r := pow_succ' _ _
    have hd : 3 ^ (j + 1) ∣ M := by rw [hM, hpow]; exact ⟨2, by ring⟩
    have hs := (Erdos287.dense_prime_power_endpoint_restrictions D m M 3 (j + 1)
      hm (by decide) (by omega) hD hmD hMD hsum hratio).2 hd (by rw [hM, hpow]; omega)
    have h3 : 3 * r ∈ D := by
      rcases hs with ⟨_, _, h⟩ | ⟨hbad, _⟩
      · simpa only [hpow] using h
      · omega
    have h6 : 6 * r ∈ D := hM ▸ hMD
    have hbound (c : ℕ) (hc : c * r ∈ D) : c ∈ Icc 3 6 :=
      cofactor_mem_interval D m M r 3 6 hD (by omega) (by omega) c hc
    have hL : ∀ n ∈ D, 3 ^ j ∣ n → n / (3 ^ j) ∣ 60 := by
      intro n hn hd'
      have h := hbound (n / r) (by rwa [Nat.div_mul_cancel hd'])
      exact (show ∀ c ∈ Icc (3 : ℕ) 6, c ∣ 60 by decide) _ h
    have hcong := Erdos287.cofactor_cut_congruence D 3 j 60 1 (by decide) hj hpos hsum hL (by decide)
    change 9 ∣ ∑ n ∈ D.filter (fun n => r ∣ n), 60 / (n / r) at hcong
    rw [sum_of_cofactors D r 60 3 6 hr hbound, sum_filter,
      show Icc (3 : ℕ) 6 = {3, 4, 5, 6} by decide] at hcong
    change 4 * r ∈ D ∧ 5 * r ∉ D
    by_cases h4 : 4 * r ∈ D <;> by_cases h5 : 5 * r ∈ D <;>
      norm_num [sum_insert, h3, h4, h5, h6] at hcong <;> simp [h4, h5]
  · intro hM
    let r := 5 ^ j
    change M = 15 * r at hM
    have hr : 0 < r := pow_pos (by decide) _
    have hpow : 5 ^ (j + 1) = 5 * r := pow_succ' _ _
    have hd : 5 ^ (j + 1) ∣ M := by rw [hM, hpow]; exact ⟨3, by ring⟩
    have hs := (Erdos287.dense_prime_power_endpoint_restrictions D m M 5 (j + 1)
      hm (by decide) (by omega) hD hmD hMD hsum hratio).2 hd (by rw [hM, hpow]; omega)
    have h10 : 10 * r ∈ D := by
      rcases hs with ⟨hbad, _⟩ | ⟨_, _, h⟩
      · omega
      · rw [hpow, show 2 * (5 * r) = 10 * r by ring] at h
        exact h
    have h15 : 15 * r ∈ D := hM ▸ hMD
    have hbound (c : ℕ) (hc : c * r ∈ D) : c ∈ Icc 6 15 :=
      cofactor_mem_interval D m M r 6 15 hD (by omega) (by omega) c hc
    have hL : ∀ n ∈ D, 5 ^ j ∣ n → n / (5 ^ j) ∣ 360360 := by
      intro n hn hd'
      have h := hbound (n / r) (by rwa [Nat.div_mul_cancel hd'])
      exact (show ∀ c ∈ Icc (6 : ℕ) 15, c ∣ 360360 by decide) _ h
    have hcong := Erdos287.cofactor_cut_congruence D 5 j 360360 1 (by decide) hj hpos hsum hL (by decide)
    change 25 ∣ ∑ n ∈ D.filter (fun n => r ∣ n), 360360 / (n / r) at hcong
    rw [sum_of_cofactors D r 360360 6 15 hr hbound] at hcong
    let C := (Icc (6 : ℕ) 14).filter (fun c => c ≠ 10)
    let S := C.filter (fun c => c * r ∈ D)
    let T := C.filter (fun c => c * r ∉ D)
    have hfull : (Icc (6 : ℕ) 15).filter (fun c => c * r ∈ D) = S ∪ {10, 15} := by
      have hbase : Icc (6 : ℕ) 15 = C ∪ {10, 15} := by decide
      rw [hbase, filter_union]
      have hfilter : ({10, 15} : Finset ℕ).filter (fun c => c * r ∈ D) = {10, 15} := by
        simp [filter_insert, filter_singleton, h10, h15]
      rw [hfilter]
    have hdisj : Disjoint S ({10, 15} : Finset ℕ) :=
      (show Disjoint C ({10, 15} : Finset ℕ) by decide).mono_left (filter_subset _ _)
    rw [hfull, sum_union hdisj] at hcong
    have hweight : ∀ c ∈ C, 360360 / c = 5 * (72072 / c) := by decide
    have hsumS : (∑ c ∈ S, 360360 / c) = 5 * ∑ c ∈ S, 72072 / c := by
      rw [mul_sum]
      exact sum_congr rfl fun c hc => hweight c ((mem_filter.mp hc).1)
    rw [hsumS, show ∑ c ∈ ({10, 15} : Finset ℕ), 360360 / c = 60060 by decide] at hcong
    have hST : (∑ c ∈ S, 72072 / c) + (∑ c ∈ T, 72072 / c) = ∑ c ∈ C, 72072 / c :=
      sum_filter_add_sum_filter_not C (fun c => c * r ∈ D) (fun c => 72072 / c)
    have htotal : (∑ c ∈ C, 72072 / c) % 5 = 0 := by decide
    have hmod : (∑ c ∈ T, 72072 / c) % 5 = 2 := by omega
    have hT : T = (Icc (6 : ℕ) 14).filter (fun c => c ≠ 10 ∧ c * r ∉ D) := by
      ext c
      simp [T, C, and_assoc]
    rw [← hT]
    refine ⟨hmod, ?_⟩
    intro c hc
    have hcT : c ∈ T := by rw [hc]; exact mem_singleton_self c
    have hcC : c ∈ C := filter_subset _ _ hcT
    have hpossible : ∀ c ∈ C, (72072 / c) % 5 = 2 → c = 6 ∨ c = 11 := by decide
    exact hpossible c hcC (by simpa [hc] using hmod)

