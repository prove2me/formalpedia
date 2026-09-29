-- Prove2me | solution 1 for BlockCycleRotation.remark_all_shifts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:55:10.187699+00:00
-- url     : https://prove2.me/submissions/78eb8579-83c0-47dc-a727-d50dfc6654cf

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_AllShifts
import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_remSum_add_gcd_le
import Theorems.Thm_BlockCycleRotation_sum_remSum_isBigO
import Theorems.Thm_BlockCycleRotation_remSum_reflect
import Theorems.Thm_BlockCycleRotation_sum_reflect_bij
import Theorems.Thm_BlockCycleRotation_sum_bigShifts_id_close
import Mathlib

open Filter Topology Finset Real

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

/-- For `2 * k ≤ n`, the remainder sum is at most `n - gcd n k`.

Stated additively to avoid truncated subtraction. -/
theorem remSum_add_gcd_le_self {n k : ℕ} (h : 2 * k ≤ n) :
    remSum n k + Nat.gcd n k ≤ n := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  -- Since `2 * k ≤ n`, the first quotient is at least `2`, so `2 * k + n % k ≤ n`.
  have hq : 2 ≤ n / k := (Nat.le_div_iff_mul_le hk).2 (by linarith)
  have : 2 * k + n % k ≤ n := by nlinarith [Nat.div_add_mod n k]
  exact le_trans (remSum_add_gcd_le k n) this

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

theorem mem_allShifts {n k : ℕ} : k ∈ allShifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n := by
  simp [allShifts]

theorem mem_bigShifts {n k : ℕ} : k ∈ bigShifts n ↔ (1 ≤ k ∧ k ≤ n) ∧ n < 2 * k := by
  rw [bigShifts, Finset.mem_filter, Finset.mem_Icc]
  omega

theorem mem_smallShifts {n j : ℕ} : j ∈ smallShifts n ↔ j < n ∧ 2 * j < n := by
  rw [smallShifts, Finset.mem_filter, Finset.mem_range]

theorem allShifts_eq_filter_prime {n : ℕ} (hn : 0 < n) :
    allShifts n = (Finset.Icc 1 n).filter (fun k => 2 * k ≤ n) := by
  ext k
  rw [mem_allShifts, Finset.mem_filter, Finset.mem_Icc]
  omega

theorem sum_Icc_split {n : ℕ} (hn : 0 < n) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 n, f k
      = (∑ k ∈ allShifts n, f k) + ∑ k ∈ bigShifts n, f k := by
  rw [allShifts_eq_filter_prime hn, bigShifts]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The upper-half remainder sums, reflected. -/
theorem sum_bigShifts_remSum {n : ℕ} :
    ∑ k ∈ bigShifts n, remSum n k
      = (∑ k ∈ bigShifts n, k) + ∑ j ∈ smallShifts n, remSum n j := by
  rw [← sum_reflect_bij, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [mem_bigShifts] at hk
  exact remSum_reflect hk.1.2 hk.2

theorem remSum_le_self {n k : ℕ} (h : 2 * k ≤ n) : remSum n k ≤ n := by
  have := remSum_add_gcd_le_self h
  omega

theorem sum_smallShifts_le {n : ℕ} (hn : 0 < n) :
    ∑ j ∈ smallShifts n, remSum n j ≤ ∑ k ∈ allShifts n, remSum n k := by
  have h0 : (0 : ℕ) ∉ allShifts n := by
    rw [mem_allShifts]
    omega
  have hsub : smallShifts n ⊆ insert 0 (allShifts n) := by
    intro j hj
    rw [mem_smallShifts] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (mem_allShifts.2 ⟨by omega, hj0, by omega⟩)
  calc ∑ j ∈ smallShifts n, remSum n j
      ≤ ∑ j ∈ insert 0 (allShifts n), remSum n j :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ k ∈ allShifts n, remSum n k := by
        rw [Finset.sum_insert h0, remSum_zero, zero_add]

theorem sum_allShifts_le_smallShifts {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, remSum n k ≤ (∑ j ∈ smallShifts n, remSum n j) + n := by
  have hsub : allShifts n ⊆ insert (n / 2) (smallShifts n) := by
    intro k hk
    obtain ⟨hkn, hk1, hk2⟩ := mem_allShifts.1 hk
    rcases lt_or_eq_of_le hk2 with hlt | heq
    · exact Finset.mem_insert_of_mem (mem_smallShifts.2 ⟨by omega, by omega⟩)
    · have hk' : k = n / 2 := by omega
      rw [hk']
      exact Finset.mem_insert_self _ _
  have hmid : remSum n (n / 2) ≤ n := remSum_le_self (by omega)
  refine le_trans (Finset.sum_le_sum_of_subset hsub) ?_
  by_cases hm : n / 2 ∈ smallShifts n
  · rw [Finset.insert_eq_self.2 hm]
    omega
  · rw [Finset.sum_insert hm]
    omega

/-- Summing over all shifts counts the lower half twice, up to the midpoint
term and `∑_{k > n/2} k`. -/
theorem sum_Icc_bounds {n : ℕ} (hn : 0 < n) :
    2 * (∑ k ∈ allShifts n, remSum n k) + (∑ k ∈ bigShifts n, k)
        ≤ (∑ k ∈ Finset.Icc 1 n, remSum n k) + n
      ∧ (∑ k ∈ Finset.Icc 1 n, remSum n k)
        ≤ 2 * (∑ k ∈ allShifts n, remSum n k) + (∑ k ∈ bigShifts n, k) := by
  have hS := sum_Icc_split hn (fun k => remSum n k)
  have hbig := sum_bigShifts_remSum (n := n)
  have h1 := sum_smallShifts_le hn
  have h2 := sum_allShifts_le_smallShifts hn
  omega

end BlockCycleRotation

open BlockCycleRotation in
/-- **The remark.**  The remainder sum averaged over `1 ≤ k ≤ n` is
`(3/8 + 2C)·n + O(n^{1/2+ε})`. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((∑ k ∈ Finset.Icc 1 n, remSum n k : ℕ) : ℝ) / (n : ℝ)
          - (3 / 8 + 2 * cConst) * (n : ℝ)|
        ≤ K * (n : ℝ) ^ (1 / 2 + ε):= by
  obtain ⟨K1, hK1, hA⟩ := sum_remSum_isBigO hε
  refine ⟨2 * K1 + 2, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε : ℝ) := Real.one_le_rpow hnR (by linarith)
  set S : ℝ := ((∑ k ∈ Finset.Icc 1 n, remSum n k : ℕ) : ℝ) with hSdef
  set A : ℝ := ((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ) with hAdef
  set B : ℝ := ((∑ k ∈ bigShifts n, k : ℕ) : ℝ) with hBdef
  obtain ⟨hb1, hb2⟩ := sum_Icc_bounds hn
  have hb1R : 2 * A + B ≤ S + (n : ℝ) := by rw [hSdef, hAdef, hBdef]; exact_mod_cast hb1
  have hb2R : S ≤ 2 * A + B := by rw [hSdef, hAdef, hBdef]; exact_mod_cast hb2
  have hAb : |A - cConst * (n : ℝ) ^ 2| ≤ K1 * (n : ℝ) ^ (3 / 2 + ε : ℝ) := hA n hn
  have hBb : |B - 3 * (n : ℝ) ^ 2 / 8| ≤ (n : ℝ) := sum_bigShifts_id_close hn
  -- the numerator estimate
  have hnum : |S - (3 / 8 + 2 * cConst) * (n : ℝ) ^ 2|
      ≤ 2 * (K1 * (n : ℝ) ^ (3 / 2 + ε : ℝ)) + 2 * (n : ℝ) := by
    rw [abs_le] at hAb hBb ⊢
    constructor <;> linarith [hAb.1, hAb.2, hBb.1, hBb.2, hb1R, hb2R]
  -- divide by `n`
  have hdiv : S / (n : ℝ) - (3 / 8 + 2 * cConst) * (n : ℝ)
      = (S - (3 / 8 + 2 * cConst) * (n : ℝ) ^ 2) / (n : ℝ) := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
  have hr : (n : ℝ) ^ (3 / 2 + ε : ℝ) = (n : ℝ) ^ (1 / 2 + ε : ℝ) * (n : ℝ) := by
    rw [show (3 / 2 + ε : ℝ) = (1 / 2 + ε) + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
  rw [hr] at hnum
  nlinarith [hnum, hpow, hnpos, hK1]
