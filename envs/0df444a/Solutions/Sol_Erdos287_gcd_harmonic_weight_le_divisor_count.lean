-- Prove2me | solution 1 for Erdos287.gcd_harmonic_weight_le_divisor_count
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:07:49.410143+00:00
-- url     : https://prove2.me/submissions/99812eee-efd7-4ac9-adfc-a58904dbd2b7

import Mathlib

open Finset

set_option autoImplicit false

/-- Summing the lengths of the admissible parameter classes costs only a
divisor factor times a harmonic sum. -/
theorem solution (s B : ℕ) (hs : 0 < s) :
    (∑ n ∈ Finset.Icc 1 B, (Nat.gcd s n : ℚ) / n) ≤
      (s.divisors.card : ℚ) * ∑ j ∈ Finset.Icc 1 B, (1 : ℚ) / j := by
  classical
  let N := Icc 1 B
  let f (u n : ℕ) : ℚ := (u.totient : ℚ) / n
  have hsplit (n : ℕ) :
      (Nat.gcd s n : ℚ) / n =
        ∑ u ∈ s.divisors, (if u ∣ n then f u n else 0) := by
    have hdivs : (Nat.gcd s n).divisors = s.divisors.filter (fun u => u ∣ n) := by
      ext u
      simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
      have hs0 : s ≠ 0 := hs.ne'
      have hg0 : s.gcd n ≠ 0 := (Nat.gcd_pos_of_pos_left n hs).ne'
      tauto
    rw [← sum_filter, show (Nat.gcd s n : ℚ) = (((Nat.gcd s n).divisors.sum Nat.totient : ℕ) : ℚ)
      from congrArg (fun t : ℕ => (t : ℚ)) (Nat.sum_totient (Nat.gcd s n)).symm, Nat.cast_sum, sum_div, hdivs]
  have hu_bound (u : ℕ) (hu : u ∈ s.divisors) :
      (∑ n ∈ N, (if u ∣ n then f u n else 0)) ≤ ∑ j ∈ N, (1 : ℚ) / j := by
    rw [← sum_filter]
    let T := N.filter (fun n => u ∣ n)
    change (∑ n ∈ T, f u n) ≤ _
    have hu0 : 0 < u := Nat.pos_of_mem_divisors hu
    have hsub : (T.image (fun n => n / u)) ⊆ N := by
      intro j hj
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hj
      obtain ⟨hnN, hdu⟩ := mem_filter.mp hn
      obtain ⟨hlo, hhi⟩ := mem_Icc.mp hnN
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hlo hdu) hu0,
        (Nat.div_le_self n u).trans hhi⟩
    have hinj : Set.InjOn (fun n => n / u) (↑T : Set ℕ) := by
      intro n hn m hm he
      change n / u = m / u at he
      have hnD := (mem_filter.mp hn).2
      have hmD := (mem_filter.mp hm).2
      calc
        n = (n / u) * u := (Nat.div_mul_cancel hnD).symm
        _ = (m / u) * u := by rw [he]
        _ = m := Nat.div_mul_cancel hmD
    calc
      _ ≤ ∑ n ∈ T, (1 : ℚ) / ((n / u : ℕ) : ℚ) := by
        apply sum_le_sum
        intro n hn
        have hn0 : (0 : ℚ) < n := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).1
        have he : ((n / u : ℕ) : ℚ) * (u : ℚ) = n := by
          exact_mod_cast Nat.div_mul_cancel (mem_filter.mp hn).2
        have hj0 : (0 : ℚ) < ((n / u : ℕ) : ℚ) := by
          exact_mod_cast Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp (mem_filter.mp hn).1).1
            (mem_filter.mp hn).2) hu0
        apply (div_le_div_iff₀ hn0 hj0).mpr
        rw [one_mul, ← he]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le u) hj0.le |>.trans_eq (mul_comm _ _)
      _ = ∑ j ∈ T.image (fun n => n / u), (1 : ℚ) / j := by
        rw [sum_image (fun _ hn _ hm he => hinj hn hm he)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
  change (∑ n ∈ N, (Nat.gcd s n : ℚ) / n) ≤ (s.divisors.card : ℚ) * ∑ j ∈ N, (1 : ℚ) / j
  simp_rw [hsplit]
  rw [sum_comm]
  calc
    _ ≤ ∑ _ ∈ s.divisors, ∑ j ∈ N, (1 : ℚ) / j := sum_le_sum hu_bound
    _ = _ := by simp [nsmul_eq_mul]

