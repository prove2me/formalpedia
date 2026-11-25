-- Prove2me | solution 1 for ErdosGirth.bound_cycles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:46.455791+00:00
-- url     : https://prove2.me/submissions/f9446159-1d1c-4ba0-8a64-d8d18d709b7e

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution (g q : ℕ) (hq : 4 * (g + 1) * (2 ^ (2 * g + 3)) ^ g < q) (m : ℝ)
    (hm1 : (q : ℝ) ^ (2 * g + 3) ≤ m) (hm2 : m ≤ ((q : ℝ) + 1) ^ (2 * g + 3)) :
    2 / m * ∑ ℓ ∈ range (g + 1), (m * (1 / (q : ℝ) ^ (2 * g + 1))) ^ ℓ < 1 / 2 := by
  set K : ℝ := 2 ^ (2 * g + 3) with hK
  have hqR : (4 * (g + 1) * K ^ g : ℝ) < q := by rw [hK]; exact_mod_cast hq
  have hK1 : (1 : ℝ) ≤ K := one_le_pow₀ (by norm_num)
  have hKg : (1 : ℝ) ≤ K ^ g := one_le_pow₀ hK1
  have hq1 : (1 : ℝ) ≤ q := by nlinarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) ^ (2 * g + 1) := by positivity
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm1
  have hx0 : 0 ≤ m * (1 / (q : ℝ) ^ (2 * g + 1)) := by positivity
  have hx : m * (1 / (q : ℝ) ^ (2 * g + 1)) ≤ K * q ^ 2 := by
    rw [mul_one_div, div_le_iff₀ hqpos]
    calc m ≤ ((q : ℝ) + 1) ^ (2 * g + 3) := hm2
      _ ≤ (2 * q) ^ (2 * g + 3) := by gcongr; linarith
      _ = K * q ^ 2 * q ^ (2 * g + 1) := by rw [hK]; ring
  have hKq : (1 : ℝ) ≤ K * q ^ 2 := by nlinarith
  have hsum : ∑ ℓ ∈ range (g + 1), (m * (1 / (q : ℝ) ^ (2 * g + 1))) ^ ℓ
      ≤ (g + 1) * (K * q ^ 2) ^ g := by
    calc _ ≤ ∑ ℓ ∈ range (g + 1), (K * q ^ 2) ^ g := by
          refine sum_le_sum fun ℓ hℓ => ?_
          exact (pow_le_pow_left₀ hx0 hx ℓ).trans
            (pow_le_pow_right₀ hKq (Nat.lt_succ_iff.mp (mem_range.mp hℓ)))
      _ = (g + 1) * (K * q ^ 2) ^ g := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  calc 2 / m * ∑ ℓ ∈ range (g + 1), (m * (1 / (q : ℝ) ^ (2 * g + 1))) ^ ℓ
      ≤ 2 / (q : ℝ) ^ (2 * g + 3) * ((g + 1) * (K * q ^ 2) ^ g) := by
        gcongr
      _ = 2 * (g + 1) * K ^ g / (q : ℝ) ^ 3 := by
        field_simp
        ring
      _ ≤ 2 * (g + 1) * K ^ g / q := by
        gcongr
        · exact le_self_pow₀ hq1 (by norm_num)
      _ < 1 / 2 := by
        rw [div_lt_iff₀ hq0]; linarith
end ErdosGirth
