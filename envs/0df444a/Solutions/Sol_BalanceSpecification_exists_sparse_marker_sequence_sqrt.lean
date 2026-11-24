-- Prove2me | solution 1 for BalanceSpecification.exists_sparse_marker_sequence_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:44.491503+00:00
-- url     : https://prove2.me/submissions/20a99a8f-29aa-4c73-a73e-b6b52e0ca73e

module
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
public import Theorems.Thm_BalanceSpecification_exists_sparse_marker_sequence

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {β C : ℝ} (hβ : 1 < β)
    (hC : 1 ≤ C) (M : ℕ) :
    ∃ D : ℕ, 0 < D ∧
      (∀ n : ℕ, 2 * (D * 4 ^ n) < D * 4 ^ (n + 1)) ∧
      (∀ n : ℕ, 4 * (n + M) ≤ D * 4 ^ n) ∧
      (∀ N : ℕ, (∑ n ∈ Finset.range N,
        if 1 ≤ n then C * β ^ n / (Real.sqrt β) ^ (D * 4 ^ n + 1) else 0) ≤ 1 / 2) ∧
      (∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ D * 4 ^ n) := by
  have hρ : 1 < Real.sqrt β := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hβ
  simpa only [Real.sq_sqrt (zero_le_one.trans hβ.le)] using
    exists_sparse_marker_sequence hρ hC M
end BalanceSpecification
