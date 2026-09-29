-- Prove2me | solution 1 for BlockCycleRotation.Eterm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:33:43.967912+00:00
-- url     : https://prove2.me/submissions/3065d150-27cb-46a8-95ce-c11ca1b85ff3

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_sqrt_le_cutoff
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

theorem cTerm_nonneg (p : ℕ × ℕ) : 0 ≤ cTerm p := by
  unfold cTerm
  split
  · positivity
  · exact le_refl 0

theorem cConst_nonneg : 0 ≤ cConst :=
  tsum_nonneg fun p => cTerm_nonneg p

end BlockCycleRotation

open BlockCycleRotation in
/-- **Every per-divisor error term is `O(n^{3/2})`.**

In the bulk case `2d ≤ m` the two pieces are `(√((m-1)/d)+1)·d·m ≤ 2·n^{3/2}`
(using `d·m = n`) and `m²·3/(2N) ≤ 6·n^{3/2}` (using `√m ≤ 4√d·N` and
`m·√m·√d = m·√n`).  In the degenerate case `m < 2d` one has `m² < 2n`. -/
theorem solution {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors) :
    Eterm n d ≤ (8 + 2 * cConst) * ((n : ℝ) * Real.sqrt n):= by
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hCnn : (0 : ℝ) ≤ cConst := cConst_nonneg
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hnR
  have hsqn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  unfold Eterm
  set m := n / d with hm
  have hdm : d * m = n := Nat.mul_div_cancel' hdn
  have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  have hmn' : m ≤ n := Nat.div_le_self n d
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn'
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hdmR : (d : ℝ) * (m : ℝ) = (n : ℝ) := by exact_mod_cast hdm
  split_ifs with hcase
  · -- bulk case `2d ≤ m`
    -- first piece: `√((m-1)/d) ≤ √n`
    have hs : ((Nat.sqrt ((m - 1) / d) : ℕ) : ℝ) ≤ Real.sqrt n := by
      have hnat : Nat.sqrt ((m - 1) / d) * Nat.sqrt ((m - 1) / d) ≤ n :=
        calc Nat.sqrt ((m - 1) / d) * Nat.sqrt ((m - 1) / d) ≤ (m - 1) / d := Nat.sqrt_le _
          _ ≤ m - 1 := Nat.div_le_self _ _
          _ ≤ m := Nat.sub_le _ _
          _ ≤ n := hmn'
      refine (Real.le_sqrt (by positivity) (by positivity)).2 ?_
      have hcast : ((Nat.sqrt ((m - 1) / d) : ℕ) : ℝ) * ((Nat.sqrt ((m - 1) / d) : ℕ) : ℝ)
          ≤ (n : ℝ) := by exact_mod_cast hnat
      nlinarith [hcast]
    have hA : (((Nat.sqrt ((m - 1) / d) : ℕ) : ℝ) + 1) * ((d : ℝ) * (m : ℝ))
        ≤ 2 * ((n : ℝ) * Real.sqrt n) := by
      rw [hdmR]
      nlinarith [hs, hsn, hnR]
    -- second piece: the cut-off is at least `√m/(4√d)`
    have hN1 : 1 ≤ Nat.sqrt (m / (2 * d)) :=
      Nat.sqrt_pos.2 ((Nat.one_le_div_iff (by omega)).2 hcase)
    have hNR : (1 : ℝ) ≤ ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ) := by exact_mod_cast hN1
    have hcut := sqrt_le_cutoff hd0 hcase
    have hsm : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt hmR
    have hsd : Real.sqrt (m : ℝ) * Real.sqrt (d : ℝ) = Real.sqrt n := by
      rw [← Real.sqrt_mul hmR]
      congr 1
      rw [← hdmR]; ring
    have hkey : (m : ℝ) * (m : ℝ)
        ≤ 4 * ((m : ℝ) * (Real.sqrt n * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ))) := by
      have h1 : (m : ℝ) * Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)
          ≤ (m : ℝ) * Real.sqrt (m : ℝ)
              * (4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcut (by positivity)
      have h2 : (m : ℝ) * Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) * (m : ℝ) := by
        rw [mul_assoc, hsm]
      have h3 : (m : ℝ) * Real.sqrt (m : ℝ)
            * (4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ))
          = 4 * ((m : ℝ) * ((Real.sqrt (m : ℝ) * Real.sqrt (d : ℝ))
              * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ))) := by ring
      rw [h2, h3, hsd] at h1
      exact h1
    have hB : (m : ℝ) ^ 2 * (3 / (2 * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)))
        ≤ 6 * ((n : ℝ) * Real.sqrt n) := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have hslack : (0 : ℝ)
          ≤ ((n : ℝ) - (m : ℝ)) * (Real.sqrt n * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith [hkey, hslack]
    nlinarith [hA, hB, mul_nonneg hCnn (mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ)) hsqn)]
  · -- degenerate case `m < 2d`
    have hlt : m * m < 2 * n := by
      have hm2 : m < 2 * d := by omega
      calc m * m < 2 * d * m := (Nat.mul_lt_mul_right hm0).2 hm2
        _ = 2 * n := by rw [← hdm]; ring
    have hltR : (m : ℝ) ^ 2 < 2 * (n : ℝ) := by
      rw [pow_two]; exact_mod_cast hlt
    have h1 : (m : ℝ) ^ 2 * cConst ≤ (2 * (n : ℝ)) * cConst :=
      mul_le_mul_of_nonneg_right hltR.le hCnn
    have h2 : (0 : ℝ) ≤ cConst * ((n : ℝ) * (Real.sqrt n - 1)) :=
      mul_nonneg hCnn (mul_nonneg (by linarith) (by linarith))
    have h3 : (0 : ℝ) ≤ 8 * ((n : ℝ) * Real.sqrt n) :=
      by positivity
    nlinarith [h1, h2, h3]
