-- Prove2me | solution 1 for FockSPR.eta_5_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:15:01.77181+00:00
-- url     : https://prove2.me/submissions/f16c7a33-06e4-4b6b-ab0a-e0bc3cd49c5d

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LeakageEstimate
section
@[expose] public section
open MeasureTheory Real Finset Complex
noncomputable section
namespace FockSPR
private lemma exp_quarter_lt : Real.exp (1 / 4 : ℝ) < 13 / 10 := by
  have h := Real.exp_bound'
    (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1:ℝ)/4 ≤ 1) (n := 5) (by norm_num)
  simp [Finset.sum_range_succ] at h; linarith only [h]
private lemma exp_neg_25_lt : Real.exp (-25 : ℝ) < 14 / 10 ^ 12 := by
  have h5 : (1484 : ℝ) / 10 ≤ Real.exp 5 := by
    have := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 5) 18
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    norm_num at this ⊢; linarith only [this]
  rw [show (-25 : ℝ) = (5 : ℕ) * (-5 : ℝ) from by norm_num,
      Real.exp_nat_mul, Real.exp_neg, inv_pow]
  calc (Real.exp 5 ^ 5)⁻¹
      ≤ ((1484 / 10 : ℝ) ^ 5)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h5 5)
    _ < 14 / 10 ^ 12 := by norm_num
private lemma exp_neg_36_lt : Real.exp (-36 : ℝ) < 1 / 10 ^ 14 := by
  have h6 : (403 : ℝ) ≤ Real.exp 6 := by
    have := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 6) 16
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    norm_num at this ⊢; linarith only [this]
  rw [show (-36 : ℝ) = (6 : ℕ) * (-6 : ℝ) from by norm_num,
      Real.exp_nat_mul, Real.exp_neg, inv_pow]
  calc (Real.exp 6 ^ 6)⁻¹
      ≤ ((403 : ℝ) ^ 6)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h6 6)
    _ < 1 / 10 ^ 14 := by norm_num
end FockSPR
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Real Finset Complex
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution : etaCoeff 5 100 < 4 / (10 : ℝ) ^ 11 := by
  unfold etaCoeff
  -- Split sum: Σ_{m=5}^{100} exp(-m²) = exp(-25) + Σ_{m=6}^{100} exp(-m²)
  have hsplit : ∑ m ∈ (Finset.Icc 5 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) =
    Real.exp (-25) + ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) := by
    rw [show (Finset.Icc 5 100 : Finset ℕ) = insert 5 (Finset.Icc 6 100) from by
      ext m; simp [Finset.mem_Icc]; omega]
    rw [Finset.sum_insert (by decide)]
    congr 1; norm_num
  rw [hsplit]
  -- Bound the tail: Σ_{m=6}^{100} exp(-m²) ≤ 95 · exp(-36)
  have htail : ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) ≤
      95 * Real.exp (-36) := by
    calc ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2)
        ≤ ∑ _m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-36 : ℝ) :=
          Finset.sum_le_sum fun m hm => by
            apply Real.exp_le_exp.mpr
            simp only [Finset.mem_Icc] at hm
            have hm6 : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
            linarith only [hm6, sq_nonneg ((m : ℝ) - 6)]
      _ = 95 * Real.exp (-36) := by simp [Finset.sum_const]
  -- Combine bounds
  have htail_bound : ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) <
      95 / 10 ^ 14 := by linarith only [htail, exp_neg_36_lt]
  have hsum_bound :
      Real.exp (-25) + ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) <
      14 / 10 ^ 12 + 95 / 10 ^ 14 := by linarith only [htail_bound, exp_neg_25_lt]
  have hsum_pos :
      0 ≤ Real.exp (-25) +
        ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) :=
    add_nonneg (le_of_lt (Real.exp_pos _))
      (Finset.sum_nonneg fun m _ => le_of_lt (Real.exp_pos _))
  -- 2 · exp(1/4) · sum < 2 · (13/10) · (14/10¹² + 95/10¹⁴) = 3887/10¹⁴ < 4/10¹¹
  have step1 : 2 * Real.exp (1 / 4) *
      (Real.exp (-25) + ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2)) <
      2 * (13 / 10) * (14 / 10 ^ 12 + 95 / 10 ^ 14) := by
    nlinarith only [hsum_bound, exp_quarter_lt, Real.exp_pos (1 / 4 : ℝ)]
  linarith only [
    step1,
    show (2 : ℝ) * (13 / 10) * (14 / 10 ^ 12 + 95 / 10 ^ 14) < 4 / 10 ^ 11 from by norm_num
  ]
end FockSPR
