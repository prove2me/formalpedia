-- Prove2me | solution 1 for BlockCycleRotation.theorem13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:29:22.168582+00:00
-- url     : https://prove2.me/submissions/059d96f7-feb0-4c48-bf39-d38fa7bf667d

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_cost_add_gcd
import Theorems.Thm_BlockCycleRotation_cost_le_three_mul
import Theorems.Thm_BlockCycleRotation_exists_card_divisors_le
import Theorems.Thm_BlockCycleRotation_sum_allShifts_eq
import Theorems.Thm_BlockCycleRotation_sum_remSum_isBigO
import Theorems.Thm_BlockCycleRotation_sum_min_eq
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

theorem mem_shifts {n k : ℕ} :
    k ∈ shifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.gcd n k = 1 := by
  simp [shifts]

theorem mem_allShifts {n k : ℕ} : k ∈ allShifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n := by
  simp [allShifts]

/-- The gcds, aggregated over the gcd. -/
theorem sum_gcd_allShifts {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, Nat.gcd n k = ∑ g ∈ n.divisors, g * (shifts (n / g)).card := by
  rw [sum_allShifts_eq hn (fun g _ => g)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The shifts of `m` number at most `m`. -/
theorem card_shifts_le (m : ℕ) : (shifts m).card ≤ m := by
  have hsub : shifts m ⊆ Finset.Icc 1 m := by
    intro k hk
    obtain ⟨hkm, hk1, hk2, -⟩ := mem_shifts.1 hk
    exact Finset.mem_Icc.2 ⟨hk1, hkm⟩
  calc (shifts m).card ≤ (Finset.Icc 1 m).card := Finset.card_le_card hsub
    _ = m := by simp

/-- **`∑ gcd(n,k) ≤ n · d(n)`.** -/
theorem sum_gcd_le {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, Nat.gcd n k ≤ n * n.divisors.card := by
  rw [sum_gcd_allShifts hn, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  obtain ⟨hgn, -⟩ := Nat.mem_divisors.1 hg
  have hmul : g * (n / g) = n := Nat.mul_div_cancel' hgn
  calc g * (shifts (n / g)).card ≤ g * (n / g) := Nat.mul_le_mul_left _ (card_shifts_le _)
    _ = n := hmul
    _ = n * 1 := (Nat.mul_one n).symm

theorem card_allShifts (n : ℕ) : (allShifts n).card = n / 2 := by
  have h : allShifts n = Finset.Icc 1 (n / 2) := by
    ext k
    rw [mem_allShifts, Finset.mem_Icc]
    omega
  rw [h, Nat.card_Icc]
  omega

/-- **The total cost over all shifts.** -/
theorem sum_algCost_eq {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, algCost n k) + (if 2 ∣ n then cost n (n / 2) else 0)
      = 2 * ∑ j ∈ allShifts n, cost n j := by
  have h0 : algCost n 0 = 0 := by
    unfold algCost
    simp [cost_zero]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn, h0, zero_add]
  exact sum_min_eq hn (cost n)

/-- **The cost over the shifts, via `cost + gcd = n + 2·remSum`.** -/
theorem sum_cost_allShifts {n : ℕ} (hn : 0 < n) :
    (∑ j ∈ allShifts n, cost n j) + ∑ j ∈ allShifts n, Nat.gcd n j
      = (n / 2) * n + 2 * ∑ j ∈ allShifts n, remSum n j := by
  rw [← Finset.sum_add_distrib]
  have hc : ∀ j ∈ allShifts n, cost n j + Nat.gcd n j = n + 2 * remSum n j :=
    fun j _ => cost_add_gcd j n
  rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib, Finset.sum_const, card_allShifts,
    smul_eq_mul, Finset.mul_sum]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Theorem 13.**  `avgCost n = D·n + O(n^{1/2+ε})` with `D = 1 + 4C ≈ 1.85`. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |avgCost n - dConst * (n : ℝ)| ≤ K * (n : ℝ) ^ (1 / 2 + ε):= by
  obtain ⟨K1, hK1, hS⟩ := sum_remSum_isBigO hε
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le hε
  refine ⟨4 * K1 + 2 * C0 + 4, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε : ℝ) := Real.one_le_rpow hnR (by linarith)
  -- the three ingredients, in `ℝ`
  set corr : ℕ := if 2 ∣ n then cost n (n / 2) else 0 with hcorr
  have hcorrle : corr ≤ 3 * n := by
    rw [hcorr]
    split_ifs with h
    · exact cost_le_three_mul (by omega)
    · omega
  have hA : (∑ k ∈ Finset.range n, (algCost n k : ℝ)) + (corr : ℝ)
      = 2 * ∑ j ∈ allShifts n, (cost n j : ℝ) := by
    exact_mod_cast sum_algCost_eq hn
  have hB : (∑ j ∈ allShifts n, (cost n j : ℝ)) + ((∑ j ∈ allShifts n, Nat.gcd n j : ℕ) : ℝ)
      = ((n / 2 : ℕ) : ℝ) * (n : ℝ) + 2 * ((∑ j ∈ allShifts n, remSum n j : ℕ) : ℝ) := by
    exact_mod_cast sum_cost_allShifts hn
  set S : ℝ := ((∑ j ∈ allShifts n, remSum n j : ℕ) : ℝ) with hSdef
  set G : ℝ := ((∑ j ∈ allShifts n, Nat.gcd n j : ℕ) : ℝ) with hGdef
  have hGnn : (0 : ℝ) ≤ G := by rw [hGdef]; positivity
  have hcorrnn : (0 : ℝ) ≤ (corr : ℝ) := by positivity
  have hcorrR : (corr : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hcorrle
  have hGle : G ≤ (n : ℝ) * (C0 * (n : ℝ) ^ ε) := by
    have h1 : G ≤ (n : ℝ) * (n.divisors.card : ℝ) := by
      rw [hGdef]; exact_mod_cast sum_gcd_le hn
    have h2 : (n : ℝ) * (n.divisors.card : ℝ) ≤ (n : ℝ) * (C0 * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (hCd n hn.ne') (by linarith)
    linarith
  -- the rounding of `n/2`
  have hhalf : |2 * ((n / 2 : ℕ) : ℝ) * (n : ℝ) - (n : ℝ) ^ 2| ≤ (n : ℝ) := by
    have h1 : 2 * (n / 2) ≤ n := by omega
    have h2 : n ≤ 2 * (n / 2) + 1 := by omega
    have h1R : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have h2R : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    rw [abs_le]
    constructor <;> nlinarith
  -- assemble the numerator
  have hnum : (∑ k ∈ Finset.range n, (algCost n k : ℝ)) - dConst * (n : ℝ) ^ 2
      = (2 * ((n / 2 : ℕ) : ℝ) * (n : ℝ) - (n : ℝ) ^ 2)
        + 4 * (S - cConst * (n : ℝ) ^ 2) - 2 * G - (corr : ℝ) := by
    rw [dConst]
    nlinarith [hA, hB]
  have hSb := hS n hn
  have key : ∀ x y z w b1 b2 b3 b4 : ℝ,
      |x| ≤ b1 → |y| ≤ b2 → 0 ≤ z → z ≤ b3 → 0 ≤ w → w ≤ b4 →
      |x + y - z - w| ≤ b1 + b2 + b3 + b4 := by
    intro x y z w b1 b2 b3 b4 h1 h2 h3 h4 h5 h6
    have e : x + y - z - w = x + y + -z + -w := by ring
    rw [e]
    calc |x + y + -z + -w| ≤ |x + y + -z| + |(-w)| := abs_add_le _ _
      _ ≤ (|x + y| + |(-z)|) + |(-w)| := by linarith [abs_add_le (x + y) (-z)]
      _ ≤ ((|x| + |y|) + |(-z)|) + |(-w)| := by linarith [abs_add_le x y]
      _ = |x| + |y| + z + w := by
          rw [abs_neg, abs_neg, abs_of_nonneg h3, abs_of_nonneg h5]
      _ ≤ b1 + b2 + b3 + b4 := by linarith
  have hy : |4 * (S - cConst * (n : ℝ) ^ 2)| ≤ 4 * (K1 * (n : ℝ) ^ (3 / 2 + ε)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    linarith [hSb]
  have hnumb : |(∑ k ∈ Finset.range n, (algCost n k : ℝ)) - dConst * (n : ℝ) ^ 2|
      ≤ (n : ℝ) + 4 * (K1 * (n : ℝ) ^ (3 / 2 + ε)) + 2 * ((n : ℝ) * (C0 * (n : ℝ) ^ ε))
        + 3 * (n : ℝ) := by
    rw [hnum]
    exact key _ _ _ _ _ _ _ _ hhalf hy (by linarith) (by linarith) hcorrnn hcorrR
  -- divide by `n`
  have havg : avgCost n - dConst * (n : ℝ)
      = ((∑ k ∈ Finset.range n, (algCost n k : ℝ)) - dConst * (n : ℝ) ^ 2) / (n : ℝ) := by
    rw [avgCost]
    field_simp
  rw [havg, abs_div, abs_of_nonneg (le_of_lt hnpos), div_le_iff₀ hnpos]
  refine hnumb.trans ?_
  have hr1 : (n : ℝ) ^ (3 / 2 + ε : ℝ) = (n : ℝ) ^ (1 / 2 + ε : ℝ) * (n : ℝ) := by
    rw [show (3 / 2 + ε : ℝ) = (1 / 2 + ε) + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
  have hr2 : (n : ℝ) ^ (ε : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  rw [hr1]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hr2) hnpos.le) hC0.le,
    mul_nonneg (sub_nonneg.2 hpow) hnpos.le, hK1, hnpos, hpow]
