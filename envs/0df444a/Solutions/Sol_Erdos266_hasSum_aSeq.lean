-- Prove2me | solution 1 for Erdos266.hasSum_aSeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:21:31.265807+00:00
-- url     : https://prove2.me/submissions/6f50e07d-f195-418b-831b-15adcd45cb28

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_term_nonneg
public import Theorems.Thm_Erdos266_pSum_tendsto
public import Theorems.Thm_Erdos266_pSum_le

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (i' : ℕ) :
    HasSum (fun n => f (i' + 1) ((aSeq n : ℕ) : ℝ)) ((xinf i' : ℚ) : ℝ) := by
  set n₀ : ℕ := cnt (4 * i' + 4) with hn₀
  have hsum : Summable (fun n => f (i' + 1) ((aSeq n : ℕ) : ℝ)) := by
    refine (summable_nat_add_iff n₀).mp ?_
    refine summable_of_sum_range_le (c := ((xinf i' : ℚ) : ℝ) - pSum i' n₀)
      (fun m => term_nonneg (by omega)) fun m => ?_
    have e1 : ∑ x ∈ range m, f (i' + 1) ((aSeq (x + n₀) : ℕ) : ℝ)
        = pSum i' (n₀ + m) - pSum i' n₀ := by
      rw [pSum, sum_range_add, ← pSum]
      have e2 : ∀ x ∈ range m, f (i' + 1) ((aSeq (n₀ + x) : ℕ) : ℝ)
          = f (i' + 1) ((aSeq (x + n₀) : ℕ) : ℝ) := by
        intro x _
        rw [Nat.add_comm n₀ x]
      rw [sum_congr rfl e2]
      ring
    rw [e1]
    have h3 := pSum_le (i' := i') (n := n₀ + m) (by omega)
    linarith
  have h4 := hsum.hasSum
  have h5 := h4.tendsto_sum_nat
  have h6 : (∑' n, f (i' + 1) ((aSeq n : ℕ) : ℝ)) = ((xinf i' : ℚ) : ℝ) := by
    refine tendsto_nhds_unique h5 ?_
    have : (fun n => ∑ m ∈ range n, f (i' + 1) ((aSeq m : ℕ) : ℝ))
        = fun n => pSum i' n := rfl
    rw [this]
    exact pSum_tendsto i'
  rwa [h6] at h4
end Erdos266
