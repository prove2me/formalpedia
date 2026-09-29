-- Prove2me | solution 1 for BlockCycleRotation.sqrt_le_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:32:42.679599+00:00
-- url     : https://prove2.me/submissions/6756a335-822e-4856-b506-b27596200be1

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

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
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

/-- `q ≤ 4·(√q)²`. -/
theorem le_four_mul_sqrt_sq {q : ℕ} (hq : 1 ≤ q) :
    q ≤ 4 * (Nat.sqrt q * Nat.sqrt q) := by
  have hs : 1 ≤ Nat.sqrt q := Nat.sqrt_pos.2 hq
  have h := Nat.lt_succ_sqrt' q
  nlinarith

/-- **The cut-off is large enough.**  `m ≤ 16·d·N²`. -/
theorem cutoff_lower {m d : ℕ} (hd : 0 < d) (h : 2 * d ≤ m) :
    m ≤ 16 * d * (Nat.sqrt (m / (2 * d)) * Nat.sqrt (m / (2 * d))) := by
  have hd2 : 0 < 2 * d := by omega
  have hq1 : 1 ≤ m / (2 * d) := (Nat.one_le_div_iff hd2).2 h
  have hlt : m < 2 * d * (m / (2 * d)) + 2 * d := by
    have hdm := Nat.div_add_mod m (2 * d)
    have hmod : m % (2 * d) < 2 * d := Nat.mod_lt m hd2
    omega
  have h4 : m / (2 * d) ≤ 4 * (Nat.sqrt (m / (2 * d)) * Nat.sqrt (m / (2 * d))) :=
    le_four_mul_sqrt_sq hq1
  nlinarith

end BlockCycleRotation

open BlockCycleRotation in
/-- **`√m ≤ 4√d·N`**, the real form of `cutoff_lower`. -/
theorem solution {m d : ℕ} (hd : 0 < d) (h : 2 * d ≤ m) :
    Real.sqrt (m : ℝ)
      ≤ 4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ):= by
  have hN : (0 : ℝ) ≤ ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ) := by positivity
  have hdR : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hkey : (m : ℝ)
      ≤ (4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)) ^ 2 := by
    have h1 : (m : ℝ) ≤ 16 * (d : ℝ)
        * (((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)) := by
      exact_mod_cast cutoff_lower hd h
    have hsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdR
    nlinarith [hsq, h1]
  calc Real.sqrt (m : ℝ)
      ≤ Real.sqrt ((4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = 4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ) :=
        Real.sqrt_sq (by positivity)
