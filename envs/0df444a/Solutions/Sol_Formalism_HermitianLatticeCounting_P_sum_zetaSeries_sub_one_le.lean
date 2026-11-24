-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sum_zetaSeries_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:12.660681+00:00
-- url     : https://prove2.me/submissions/f095c940-36be-4165-a54c-fd85e9b7612a

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_summable_one_div_add_two_pow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_zetaSeries_eq_one_add_tsum
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_tsum_one_div_add_two_sq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sum_Icc_three_pow_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
private theorem hasSum_inv_succ_sub_inv_succ_succ_eq_one :
    HasSum (fun n : ℕ => 1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2)) 1 := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2) := by
    intro n
    have h1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le h1 (by linarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have e : ∀ M : ℕ, ∑ i ∈ Finset.range M, (1 / ((i:ℝ) + 1) - 1 / ((i:ℝ) + 2)) =
      1 - 1 / ((M:ℝ) + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ, show (M:ℝ) + 1 + 1 = M + 2 by ring]; ring
  simp_rw [e]
  have := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1:ℝ)) Filter.atTop (nhds 1)).sub
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using this
private theorem hasSum_finset_sum_of_forall_hasSum {γ : Type*} [DecidableEq γ] (s : Finset γ) (f : γ → ℕ → ℝ)
    (a : γ → ℝ) : (∀ i ∈ s, HasSum (f i) (a i)) →
      HasSum (fun n => ∑ i ∈ s, f i n) (∑ i ∈ s, a i) := by
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact hasSum_zero
  · intro i s hi ih h
    have e1 : (fun n => ∑ j ∈ insert i s, f j n) = fun n => f i n + ∑ j ∈ s, f j n := by
      funext n; rw [Finset.sum_insert hi]
    rw [e1, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
private theorem inv_cube_div_one_sub_inv_eq_of_eq_add_one (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : b = a + 1) :
    (1 / b) ^ 3 / (1 - 1 / b) = 1 / a - 1 / b - 1 / b ^ 2 := by
  have e1 : 1 - 1 / b = a / b := by
    rw [eq_div_iff hb, sub_mul, one_div, inv_mul_cancel₀ hb, hab]; ring
  have ha' : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hb' : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  rw [e1, div_div_eq_mul_div, div_eq_iff ha]
  linear_combination (b⁻¹ ^ 2 + 1 + b⁻¹) * hb' - ha' - (b⁻¹ + b⁻¹ ^ 2) * hab
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (N : ℕ) : ∑ j ∈ Finset.Icc 3 N, (zetaR j - 1) ≤ 0.356 := by
  have hH : HasSum (fun n : ℕ => ∑ j ∈ Finset.Icc 3 N, (1 / ((n:ℝ) + 2)) ^ j)
      (∑ j ∈ Finset.Icc 3 N, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1)) := by
    apply hasSum_finset_sum_of_forall_hasSum
    intro j hj
    have hj2 : 2 ≤ j := by simp only [Finset.mem_Icc] at hj; omega
    show HasSum (fun n : ℕ => (1 / ((n:ℝ) + 2)) ^ j) (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1)
    have e : (fun n : ℕ => (1 / ((n:ℝ) + 2)) ^ j) = fun n : ℕ => 1 / ((n:ℝ) + 2) ^ j := by
      funext n; exact _root_.one_div_pow _ _
    rw [e, show Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1 = ∑' n : ℕ, 1 / ((n:ℝ) + 2) ^ j by
      rw [zetaSeries_eq_one_add_tsum j hj2]; ring]
    exact (summable_one_div_add_two_pow j hj2).hasSum
  have hb : ∀ n : ℕ, ∑ j ∈ Finset.Icc 3 N, (1 / ((n:ℝ) + 2)) ^ j ≤
      (1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2)) - 1 / ((n:ℝ) + 2) ^ 2 := by
    intro n
    have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hn2 : (0:ℝ) < (n:ℝ) + 2 := by positivity
    have hx0 : 0 ≤ 1 / ((n:ℝ) + 2) := by positivity
    have hx1 : 1 / ((n:ℝ) + 2) < 1 := by rw [div_lt_one hn2]; linarith
    refine (sum_Icc_three_pow_le _ hx0 hx1 N).trans (le_of_eq ?_)
    exact inv_cube_div_one_sub_inv_eq_of_eq_add_one _ _ hn1.ne' hn2.ne' (by ring)
  have hS1 : HasSum (fun n : ℕ => (1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2)) - 1 / ((n:ℝ) + 2) ^ 2)
      (1 - (Real.pi ^ 2 / 6 - 1)) := by
    have h2 : HasSum (fun n : ℕ => 1 / ((n:ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
      rw [← tsum_one_div_add_two_sq]
      exact (summable_one_div_add_two_pow 2 le_rfl).hasSum
    exact hasSum_inv_succ_sub_inv_succ_succ_eq_one.sub h2
  have hle := hasSum_le hb hH hS1
  nlinarith [Real.pi_gt_d4]
end Formalism.HermitianLatticeCounting.P
