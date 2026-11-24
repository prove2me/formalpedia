-- Prove2me | solution 1 for BalanceSpecification.Growth.bsm_iff_bddAbove_of_rate_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:52.223273+00:00
-- url     : https://prove2.me/submissions/e32ec541-6c41-4788-905e-da27e597f74d

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Growth
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
    (hs : Submultiplicative a) (hz : rate a = 0) :
    BoundedSupermultiplicative a ↔ BddAbove (range a) := by
  constructor
  · intro h
    obtain ⟨c, hc, hb⟩ := (bsm_iff_uniform_exp_bound ha hs).mp h
    refine ⟨c, ?_⟩
    rintro _ ⟨n, rfl⟩
    simpa only [hz, mul_zero, Real.exp_zero, mul_one] using hb n
  · rintro ⟨c, hc⟩
    have hb n : a n ≤ c := hc (mem_range_self n)
    have hc1 : 1 ≤ c := (ha 0).trans (hb 0)
    have hcn : 0 ≤ c := zero_le_one.trans hc1
    refine ⟨c * c, one_le_mul_of_one_le_of_one_le hc1 hc1, ?_⟩
    intro m n
    calc
      a m * a n ≤ c * c := mul_le_mul (hb m) (hb n)
        (zero_le_one.trans (ha n)) hcn
      _ ≤ (c * c) * a (m + n) :=
        le_mul_of_one_le_right (mul_nonneg hcn hcn) (ha (m + n))
end BalanceSpecification.Growth
