-- Prove2me | solution 1 for BalanceSpecification.Growth.bsm_iff_exp_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:42.10181+00:00
-- url     : https://prove2.me/submissions/dc4fdd68-f286-4753-9899-0d65d8b2d94d

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Growth
public import Theorems.Thm_BalanceSpecification_Growth_exp_mul_rate_le
public import Theorems.Thm_BalanceSpecification_Growth_bsm_iff_uniform_exp_bound

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
      ∃ c : ℝ, 1 ≤ c ∧ ∀ n : ℕ,
        1 / c ≤ Real.exp ((n : ℝ) * rate a) / a n ∧
          Real.exp ((n : ℝ) * rate a) / a n ≤ 1 := by
  rw [bsm_iff_uniform_exp_bound ha hs]
  constructor
  · rintro ⟨c, hc, hb⟩
    have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
    refine ⟨c, hc, fun n => ⟨?_, ?_⟩⟩
    · apply (div_le_div_iff₀ hcp (lt_of_lt_of_le zero_lt_one (ha n))).mpr
      simpa only [one_mul, mul_one, mul_comm] using hb n
    · exact (div_le_one (lt_of_lt_of_le zero_lt_one (ha n))).mpr
        (exp_mul_rate_le ha hs n)
  · rintro ⟨c, hc, hb⟩
    have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
    refine ⟨c, hc, fun n => ?_⟩
    have H := (div_le_div_iff₀ hcp (lt_of_lt_of_le zero_lt_one (ha n))).mp (hb n).1
    simpa only [one_mul, mul_one, mul_comm] using H
end BalanceSpecification.Growth
