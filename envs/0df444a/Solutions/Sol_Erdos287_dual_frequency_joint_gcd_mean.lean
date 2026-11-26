-- Prove2me | solution 1 for Erdos287.dual_frequency_joint_gcd_mean
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T21:00:22.015445+00:00
-- url     : https://prove2.me/submissions/0fe2cf70-3dff-4254-889a-687e413ed8cb

import Mathlib

open Finset

set_option autoImplicit false

private theorem single_gcd_mean (H M : ℕ) (hM : 0 < M) :
    (∑ t ∈ Ioc 0 H, t.gcd M) ≤ H * M.divisors.card := by
  classical
  have hsplit (t : ℕ) (ht : t ∈ Ioc 0 H) :
      t.gcd M = ∑ d ∈ M.divisors, if d ∣ t then d.totient else 0 := by
    have hd : (t.gcd M).divisors = M.divisors.filter (fun d => d ∣ t) := by
      ext d
      have ht0 : 0 < t := (mem_Ioc.mp ht).1
      have hg : 0 < t.gcd M := Nat.gcd_pos_of_pos_left _ ht0
      have hM0 : M ≠ 0 := hM.ne'
      have hg0 : t.gcd M ≠ 0 := hg.ne'
      simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
      tauto
    rw [← sum_filter, ← hd, Nat.sum_totient]
  have hclass (d : ℕ) :
      (∑ t ∈ Ioc 0 H, if d ∣ t then d.totient else 0) ≤ H := by
    rw [← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]
    exact (Nat.mul_le_mul_left _ (Nat.totient_le d)).trans (Nat.div_mul_le_self H d)
  calc
    _ = ∑ t ∈ Ioc 0 H, ∑ d ∈ M.divisors, if d ∣ t then d.totient else 0 :=
      sum_congr rfl hsplit
    _ = ∑ d ∈ M.divisors, ∑ t ∈ Ioc 0 H, if d ∣ t then d.totient else 0 := sum_comm
    _ ≤ ∑ _ ∈ M.divisors, H := sum_le_sum fun d _ => hclass d
    _ = H * M.divisors.card := by simp [Nat.mul_comm]

/-- The simultaneous gcd weight in the Type III dual frequency has a
divisor-bound mean when the three modulus parts are coprime. -/
theorem solution (H r j e : ℕ) (hpos : 0 < r * j * e)
    (hrj : r.Coprime j) (he : (r * j).Coprime e) :
    (∑ t ∈ Finset.Ioc 0 H, t.gcd r * t.gcd j * t.gcd e) ≤
      H * (r.divisors.card * j.divisors.card * e.divisors.card) := by
  have hterm (t : ℕ) :
      t.gcd r * t.gcd j * t.gcd e ≤ t.gcd (r * j * e) := by
    have hd : t.gcd r * t.gcd j ∣ r * j :=
      Nat.mul_dvd_mul (Nat.gcd_dvd_right t r) (Nat.gcd_dvd_right t j)
    have ht : t.gcd r * t.gcd j ∣ t :=
      (hrj.gcd_both t t).mul_dvd_of_dvd_of_dvd
        (Nat.gcd_dvd_left t r) (Nat.gcd_dvd_left t j)
    have hc : (t.gcd r * t.gcd j).Coprime (t.gcd e) :=
      (he.coprime_dvd_left hd).coprime_dvd_right (Nat.gcd_dvd_right t e)
    exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_right t hpos)
      (Nat.dvd_gcd (hc.mul_dvd_of_dvd_of_dvd ht (Nat.gcd_dvd_left t e))
        (Nat.mul_dvd_mul hd (Nat.gcd_dvd_right t e)))
  calc
    _ ≤ ∑ t ∈ Ioc 0 H, t.gcd (r * j * e) := sum_le_sum fun t _ => hterm t
    _ ≤ H * (r * j * e).divisors.card := single_gcd_mean H _ hpos
    _ = _ := by rw [he.card_divisors_mul, hrj.card_divisors_mul]

