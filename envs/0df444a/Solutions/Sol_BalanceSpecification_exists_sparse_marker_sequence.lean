-- Prove2me | solution 1 for BalanceSpecification.exists_sparse_marker_sequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:26:28.130972+00:00
-- url     : https://prove2.me/submissions/0873520c-7842-4f80-9bd0-58a7be0c6336

module
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
public import Theorems.Thm_BalanceSpecification_two_mul_add_one_le_four_pow
public import Theorems.Thm_BalanceSpecification_sum_quarter_pow_le

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {ρ C : ℝ} (hρ : 1 < ρ) (hC : 1 ≤ C) (M : ℕ) :
    ∃ D : ℕ, 0 < D ∧
      (∀ n : ℕ, 2 * (D * 4 ^ n) < D * 4 ^ (n + 1)) ∧
      (∀ n : ℕ, 4 * (n + M) ≤ D * 4 ^ n) ∧
      (∀ N : ℕ, (∑ n ∈ Finset.range N,
        if 1 ≤ n then C * (ρ ^ 2) ^ n / ρ ^ (D * 4 ^ n + 1) else 0) ≤ 1 / 2) ∧
      (∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ D * 4 ^ n) := by
  have hρpos : 0 < ρ := zero_lt_one.trans hρ
  have hev := (tendsto_pow_atTop_atTop_of_one_lt hρ).eventually
    (eventually_ge_atTop (4 * C))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  let D := max K (4 * (M + 1) + 2)
  have hDlarge : 4 * (M + 1) + 2 ≤ D := le_max_right _ _
  have hDpos : 0 < D := by omega
  have hDtwo : 2 ≤ D := by omega
  have hDfour : 4 ≤ D := by omega
  have hpower : 4 * C ≤ ρ ^ D := hK D (le_max_left _ _)
  have hbase : C ≤ ρ ^ D / 4 := (le_div_iff₀ (by norm_num)).mpr (by
    simpa only [mul_comm] using hpower)
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hsingle (n : ℕ) : C * (ρ ^ 2) ^ n / ρ ^ (D * 4 ^ n + 1) ≤
      ((1 : ℝ) / 4) ^ (n + 1) := by
    have hexponent : D * (n + 1) + 2 * n ≤ D * 4 ^ n + 1 := by
      have hfour := two_mul_add_one_le_four_pow n
      nlinarith
    have hCpow : C ≤ (ρ ^ D / 4) ^ (n + 1) := by
      calc
        C = C * 1 := (mul_one C).symm
        _ ≤ C * C ^ n := mul_le_mul_of_nonneg_left (one_le_pow₀ hC) hCp.le
        _ = C ^ (n + 1) := by rw [pow_succ]; ring
        _ ≤ (ρ ^ D / 4) ^ (n + 1) := pow_le_pow_left₀ hCp.le hbase _
    apply (div_le_iff₀ (pow_pos hρpos _)).mpr
    calc
      C * (ρ ^ 2) ^ n ≤ (ρ ^ D / 4) ^ (n + 1) * (ρ ^ 2) ^ n :=
        mul_le_mul_of_nonneg_right hCpow (pow_nonneg (sq_nonneg ρ) _)
      _ = ((1 : ℝ) / 4) ^ (n + 1) * ρ ^ (D * (n + 1) + 2 * n) := by
        rw [show ρ ^ (D * (n + 1) + 2 * n) =
          (ρ ^ D) ^ (n + 1) * (ρ ^ 2) ^ n by rw [pow_add, pow_mul, pow_mul]]
        simp only [div_pow, one_pow]
        ring
      _ ≤ ((1 : ℝ) / 4) ^ (n + 1) * ρ ^ (D * 4 ^ n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ.le hexponent)
          (pow_nonneg (by norm_num) _)
  refine ⟨D, hDpos, ?_, ?_, ?_, ?_⟩
  · intro n
    have hsp : 0 < D * 4 ^ n := Nat.mul_pos hDpos (by positivity)
    rw [pow_succ, show D * (4 ^ n * 4) = 4 * (D * 4 ^ n) by ring]
    omega
  · intro n
    have hfour := two_mul_add_one_le_four_pow n
    nlinarith
  · intro N
    calc
      _ ≤ ∑ n ∈ Finset.range N, ((1 : ℝ) / 4) ^ (n + 1) := by
        apply Finset.sum_le_sum
        intro n _
        split
        · exact hsingle n
        · exact pow_nonneg (by norm_num) _
      _ ≤ 1 / 3 := sum_quarter_pow_le N
      _ ≤ 1 / 2 := by norm_num
  · intro L
    refine ⟨max 1 L, le_max_left _ _, ?_⟩
    have hfour := two_mul_add_one_le_four_pow (max 1 L)
    have hL : L ≤ max 1 L := le_max_right _ _
    nlinarith
end BalanceSpecification
