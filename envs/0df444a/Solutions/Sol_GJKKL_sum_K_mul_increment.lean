-- Prove2me | solution 1 for GJKKL.sum_K_mul_increment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:56.182697+00:00
-- url     : https://prove2.me/submissions/0c13b5f2-3bde-4c39-85f5-04cc7cc29b2a

module
public import Definitions.Def_GJKKL_Greedy_Drift
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Theorems.Thm_GJKKL_frozen_of_uncovered
public import Theorems.Thm_GJKKL_frozen_cons_of_mem
public import Theorems.Thm_GJKKL_frozen_cons_of_not_mem
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_greedyKernel_K
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_GJKKL_mem_Dv
public import Theorems.Thm_GJKKL_mem_sdiff_Dv
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
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {v : V} {h : List (Finset V)}
    (hv : v ∉ covered h) (σ : ℝ) (φ : ℕ → ℝ) :
    ((avail H h).card : ℝ) * ∑ a, (greedyKernel H).K h a *
        (frozen H (fun t x => σ * x + φ t) v (a :: h) - frozen H (fun t x => σ * x + φ t) v h) =
      -σ * (lossSum H h v : ℝ) +
        ((avail H h \ Dv H h v).card : ℝ) * (φ (h.length + 1) - φ h.length) := by
  classical
  simp only [greedyKernel_K, ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter, mul_sum]
  -- split `A` into `A \ D` and `D`
  have hDA : Dv H h v ⊆ avail H h := filter_subset _ _
  rw [← sum_sdiff hDA]
  have hD : ∑ a ∈ Dv H h v, ((avail H h).card : ℝ) * (((avail H h).card : ℝ)⁻¹ *
      (frozen H (fun t x => σ * x + φ t) v (a :: h) -
        frozen H (fun t x => σ * x + φ t) v h)) = 0 := by
    refine sum_eq_zero fun a ha => ?_
    rw [frozen_cons_of_mem H _ h (mem_Dv.mp ha).2, sub_self, mul_zero, mul_zero]
  rw [hD, add_zero]
  have hA : (avail H h).Nonempty ∨ (avail H h \ Dv H h v) = ∅ := by
    rcases (avail H h).eq_empty_or_nonempty with h0 | h0
    · right; rw [h0]; simp
    · left; exact h0
  rcases hA with hne | hempty
  · have hcard : ((avail H h).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
    have hterm : ∀ a ∈ avail H h \ Dv H h v, ((avail H h).card : ℝ) * (((avail H h).card : ℝ)⁻¹ *
        (frozen H (fun t x => σ * x + φ t) v (a :: h) -
          frozen H (fun t x => σ * x + φ t) v h)) =
        -σ * (((Dv H h v).filter (fun f => ¬ Disjoint f a)).card : ℝ) +
          (φ (h.length + 1) - φ h.length) := by
      intro a ha
      have hva : v ∉ a := (mem_sdiff_Dv.mp ha).2
      rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, frozen_cons_of_not_mem H _ hv hva,
        frozen_of_uncovered H _ v hv]
      beta_reduce
      ring
    rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, lossSum]
    push_cast
    ring
  · rw [hempty, lossSum, hempty]
    simp
end GJKKL
