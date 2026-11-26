-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.workload_cost_lower_bound_path
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:29:15.16332+00:00
-- url     : https://prove2.me/submissions/5b58c08e-2d5c-4037-bd86-5f778a9e11e0

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_balance

open BellWilliams2001.ThresholdPolicy
open Set

set_option maxHeartbeats 700000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) (ω : Ω) (t : ℝ) (ht : 0 ≤ t)
    (hBound : BddBelow (Set.range (fun s : Set.Icc (0 : ℝ) t => M.workloadInput n T ω s))) :
    let x := M.workloadInput n T ω
    let κ := min (M.h 0) (M.h 1 / M.poolingWeight n)
    κ * (x t - ⨅ s : Set.Icc (0 : ℝ) t, x s) ≤ ∑ k, M.h k * M.Qhat n T ω t k := by
  let x := M.workloadInput n T ω
  let κ := min (M.h 0) (M.h 1 / M.poolingWeight n)
  let v (s : ℝ) := M.muR n 0 * M.Ihat n T ω s 0 + M.muR n 1 * M.Ihat n T ω s 1
  let R := M.r n^2
  have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
  have hR : 0 ≤ R := sq_nonneg _
  have hW : 0 < M.poolingWeight n := div_pos (M.muR_pos n 1) (M.muR_pos n 2)
  have hv : MonotoneOn v (Set.Ici 0) := by
    intro a ha b hb hab
    have hI (k : Fin 2) : M.Ihat n T ω a k ≤ M.Ihat n T ω b k := by
      exact div_le_div_of_nonneg_right (hT.idle_mono ω k
        (show R*a ∈ Ici (0:ℝ) from mul_nonneg hR ha)
        (show R*b ∈ Ici (0:ℝ) from mul_nonneg hR hb)
        (mul_le_mul_of_nonneg_left hab hR)) hr.le
    exact add_le_add (mul_le_mul_of_nonneg_left (hI 0) (M.muR_pos n 0).le)
      (mul_le_mul_of_nonneg_left (hI 1) (M.muR_pos n 1).le)
  have hEq (s : ℝ) : M.workload n T ω s = x s + v s := by
    rw [workload_balance M n T ω s]
    exact add_assoc _ _ _
  have hQ (s : ℝ) (hs : 0 ≤ s) (k : Fin 2) : 0 ≤ M.Qhat n T ω s k :=
    div_nonneg (hT.queue_nonneg ω k _ (mul_nonneg hR hs)) hr.le
  have hnon (s : ℝ) (hs : 0 ≤ s) : 0 ≤ M.workload n T ω s := by
    exact add_nonneg (hQ s hs 0) (mul_nonneg hW.le (hQ s hs 1))
  haveI : Nonempty (Icc (0:ℝ) t) := ⟨⟨0,le_rfl,ht⟩⟩
  have hvLower : -(v t) ≤ ⨅ s : Icc (0:ℝ) t, x s := by
    apply le_ciInf
    intro s
    have h := hnon s s.2.1
    rw [hEq] at h
    have hvt := hv (show (s:ℝ) ∈ Ici 0 from s.2.1) (show t ∈ Ici 0 from ht) s.2.2
    linarith
  have hRfl : x t-(⨅ s : Icc (0:ℝ) t, x s) ≤ M.workload n T ω t := by rw [hEq]; linarith
  have hκ : 0 ≤ κ := le_min (M.h_pos 0).le (div_nonneg (M.h_pos 1).le hW.le)
  refine (mul_le_mul_of_nonneg_left hRfl hκ).trans ?_
  have h0 : κ ≤ M.h 0 := min_le_left _ _
  have h1 : κ * M.poolingWeight n ≤ M.h 1 := (le_div_iff₀ hW).1 (min_le_right _ _)
  rw [Fin.sum_univ_two,SystemSequence.workload,mul_add,←mul_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_right h0 (hQ t ht 0))
    (mul_le_mul_of_nonneg_right h1 (hQ t ht 1))
