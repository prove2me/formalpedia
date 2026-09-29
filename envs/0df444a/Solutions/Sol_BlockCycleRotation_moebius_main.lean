-- Prove2me | solution 1 for BlockCycleRotation.moebius_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:53:26.356599+00:00
-- url     : https://prove2.me/submissions/c9c58591-6f48-4f77-9cc7-f2d0185ca2b7

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_sum_div_sq_eq
import Mathlib

open Finset Real

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The main term after Möbius inversion.** -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * (cConst * ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2)
      = cConst * (n : ℝ) ^ 2:= by
  have hbase : ∑ x ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1) • (∑ d ∈ (x.2).divisors, (d : ℝ) ^ 2) = (n : ℝ) ^ 2 :=
    ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.1 (fun _ _ => rfl) n hn
  rw [Nat.sum_divisorsAntidiagonal
    (fun x y => (ArithmeticFunction.moebius x) • (∑ e ∈ (y : ℕ).divisors, (e : ℝ) ^ 2))] at hbase
  have hstep : ∀ d ∈ n.divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)
          * (cConst * ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2)
        = cConst * ((ArithmeticFunction.moebius d) • (∑ e ∈ (n / d).divisors, (e : ℝ) ^ 2)) := by
    intro d hd
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hk : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    have hg : ∑ e ∈ (n / d).divisors, (e : ℝ) ^ 2
        = ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2 := by
      have h := sum_div_sq_eq hk (1 : ℝ)
      simp only [one_mul] at h
      rw [← h]
      exact (Nat.sum_div_divisors (n / d) (fun y => (y : ℝ) ^ 2)).symm
    rw [hg, zsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hbase]
