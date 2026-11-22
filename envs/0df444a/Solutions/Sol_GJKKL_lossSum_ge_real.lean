-- Prove2me | solution 1 for GJKKL.lossSum_ge_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:56.682952+00:00
-- url     : https://prove2.me/submissions/66194d51-3a7e-4e2a-8a71-cdef7dec93b5

module
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Definitions.Def_GJKKL_Trajectory_Trend
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Theorems.Thm_GJKKL_inner_sum_bounds
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_GJKKL_lossSum_bounds
attribute [local simp] GJKKL.Dv_nil
attribute [local simp] GJKKL.History.aliveBefore_cons
attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k)
    {dh δ : ℕ → ℝ} {h : List (Finset V)} (ht : Tracked H dh δ h) (v : V) {c : ℕ}
    (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) :
    (dv H h v : ℝ) * ((k : ℝ) - 1) * (dh h.length - δ h.length) -
        (dv H h v : ℝ) * ((((k - 1) + (k - 1) * (k - 2) : ℕ) : ℝ)) * c ≤ lossSum H h v := by
  have hb := (lossSum_bounds H hk h v hc).2
  have hbR : ∑ f ∈ Dv H h v, ∑ u ∈ f.erase v, (dv H h u : ℝ) ≤ (lossSum H h v : ℝ) +
      (dv H h v : ℝ) * (((k - 1) * c + (k - 1) * (k - 2) * c : ℕ) : ℝ) := by
    rw [dv]; exact_mod_cast hb
  have hlo : (dv H h v : ℝ) * (((k : ℝ) - 1) * (dh h.length - δ h.length)) ≤
      ∑ f ∈ Dv H h v, ∑ u ∈ f.erase v, (dv H h u : ℝ) := by
    calc (dv H h v : ℝ) * (((k : ℝ) - 1) * (dh h.length - δ h.length))
        = ∑ _f ∈ Dv H h v, ((k : ℝ) - 1) * (dh h.length - δ h.length) := by
          rw [sum_const, nsmul_eq_mul, dv]
      _ ≤ _ := sum_le_sum fun f hf => (inner_sum_bounds H hk ht hf).1
  have heq : (((k - 1) * c + (k - 1) * (k - 2) * c : ℕ) : ℝ) =
      ((((k - 1) + (k - 1) * (k - 2) : ℕ) : ℝ)) * c := by
    simp only [Nat.cast_add, Nat.cast_mul]; ring
  rw [heq] at hbR
  linarith
end GJKKL
