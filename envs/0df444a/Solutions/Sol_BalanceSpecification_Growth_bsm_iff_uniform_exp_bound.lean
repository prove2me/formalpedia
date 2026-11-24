-- Prove2me | solution 1 for BalanceSpecification.Growth.bsm_iff_uniform_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:54.347109+00:00
-- url     : https://prove2.me/submissions/6dea86c1-62ab-462e-ac03-b8cbc27e864c

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Growth
public import Theorems.Thm_BalanceSpecification_Growth_exp_mul_rate_le
public import Theorems.Thm_BalanceSpecification_Growth_le_mul_exp_rate_of_bsm

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth
namespace BalanceSpecification.Growth
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) :
    BoundedSupermultiplicative a ↔
      ∃ c : ℝ, 1 ≤ c ∧ ∀ n, a n ≤ c * Real.exp ((n : ℝ) * rate a) := by
  constructor
  · rintro ⟨c, hc, hb⟩
    exact ⟨c, hc, le_mul_exp_rate_of_bsm ha hs hc hb⟩
  · rintro ⟨c, hc, hb⟩
    have hcn : 0 ≤ c := le_trans zero_le_one hc
    refine ⟨c * c, one_le_mul_of_one_le_of_one_le hc hc, ?_⟩
    intro m n
    calc
      a m * a n ≤ (c * Real.exp ((m : ℝ) * rate a)) *
          (c * Real.exp ((n : ℝ) * rate a)) :=
        mul_le_mul (hb m) (hb n) (le_trans zero_le_one (ha n))
          (mul_nonneg hcn (Real.exp_nonneg _))
      _ = (c * c) * Real.exp (((m + n : ℕ) : ℝ) * rate a) := by
        rw [Nat.cast_add, add_mul, Real.exp_add]
        ring
      _ ≤ (c * c) * a (m + n) :=
        mul_le_mul_of_nonneg_left (exp_mul_rate_le ha hs _) (mul_nonneg hcn hcn)
end BalanceSpecification.Growth
