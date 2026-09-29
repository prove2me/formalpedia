-- Prove2me | solution 1 for BlockCycleRotation.Qgt_sub_G1_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:53:05.807647+00:00
-- url     : https://prove2.me/submissions/ed5e8467-15d2-4337-b61f-3359ba05c9fe

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem13
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_Q_gt_tripleSum
import Theorems.Thm_BlockCycleRotation_outer_layer
import Theorems.Thm_BlockCycleRotation_divisor_estimate
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
/-- **The restricted quadruple sum is `G₁` up to `O(n^{3/2+ε})`.** -/
theorem solution {n : ℕ} (hn : 0 < n) :
    |((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ) - G1 n|
      ≤ 5 * Err n:= by
  classical
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
  set Big : ℝ := ((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n)) with hBig
  have hper : ∀ d ∈ n.divisors,
      |((∑ t ∈ gtTriples (n / d) d, (d * t.1 + (n / d - t.2.1 * t.2.2) / t.1) : ℕ) : ℝ)
        - ∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
            ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
              + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p)|
        ≤ 2 * (((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
            * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ)))) + 3 * Big := by
    intro d hd
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hm0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    refine (divisor_estimate hm0 hd0).trans ?_
    -- the small part is at most `3·Big`
    have hmn : n / d ≤ n := Nat.div_le_self _ _
    have hdm : d * (n / d) = n := Nat.mul_div_cancel' hdn
    have hsq : Nat.sqrt ((n / d - 1) / d) ≤ Nat.sqrt n := by
      refine Nat.sqrt_le_sqrt ?_
      calc (n / d - 1) / d ≤ n / d - 1 := Nat.div_le_self _ _
        _ ≤ n := by omega
    have hsqR : ((Nat.sqrt ((n / d - 1) / d) : ℕ) : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) := by
      exact_mod_cast hsq
    have hbnd : ((2 * d + 2) * (2 * (n / d)) : ℕ) ≤ 8 * n := by
      have h1 : d * (n / d) ≤ n := by omega
      nlinarith
    have hbndR : (((2 * d + 2) * (2 * (n / d)) : ℕ) : ℝ) ≤ 8 * (n : ℝ) := by
      exact_mod_cast hbnd
    have hs1 : (0 : ℝ) ≤ ((Nat.sqrt ((n / d - 1) / d) : ℕ) : ℝ) := by positivity
    have hsmallbnd : (((Nat.sqrt ((n / d - 1) / d) + 1) * ((2 * d + 2) * (2 * (n / d))) : ℕ) : ℝ)
        ≤ 3 * Big := by
      calc (((Nat.sqrt ((n / d - 1) / d) + 1) * ((2 * d + 2) * (2 * (n / d))) : ℕ) : ℝ)
        = (((Nat.sqrt ((n / d - 1) / d) : ℕ) : ℝ) + 1)
            * (((2 * d + 2) * (2 * (n / d)) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (((Nat.sqrt n : ℕ) : ℝ) + 1) * (8 * (n : ℝ)) := by
            refine mul_le_mul (by linarith) hbndR (by positivity) (by positivity)
        _ ≤ 3 * Big := by
            rw [hBig]
            have h9 : (8 : ℝ) * (n : ℝ) ≤ 3 * (3 * (n : ℝ) * (1 + Real.log n)) := by nlinarith
            have hnn : (0 : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) + 1 := by positivity
            nlinarith
    linarith
  rw [Q_gt_tripleSum hn, G1, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ d ∈ n.divisors, 2 * (((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
        * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ))))
      ≤ 2 * Err n := by
    rw [← Finset.mul_sum, Err]
    exact mul_le_mul_of_nonneg_left (outer_layer hn) (by norm_num)
  have h2 : ∑ _d ∈ n.divisors, 3 * Big = 3 * Err n := by
    rw [Finset.sum_const, nsmul_eq_mul, Err, hBig]
    ring
  rw [h2]
  linarith
