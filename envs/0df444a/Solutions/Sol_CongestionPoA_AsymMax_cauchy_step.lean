-- Prove2me | solution 1 for CongestionPoA.AsymMax.cauchy_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:18:18.767388+00:00
-- url     : https://prove2.me/submissions/cef60578-58c0-4f22-b155-07b377ae3568

import Definitions.Def_CongestionPoA_AsymMax_Model
set_option autoImplicit false
open CongestionPoA.AsymMax

theorem dc {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (g : E → ℝ) :
    ∑ i, ∑ e ∈ A i, g e = ∑ e, (load A e : ℝ) * g e := by
  have h : ∀ i, ∑ e ∈ A i, g e = ∑ e, if e ∈ A i then g e else 0 := fun i => by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_filter]
  simp [load, mul_comm]

theorem sumCost_eq {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A : ι → Finset E) :
    sumCost G A = ∑ e, (load A e : ℝ) * G.latency e (load A e) :=
  dc A (fun e => G.latency e (load A e))

theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e n, G.latency e n = a e * n + b e)
    (A : ι → Finset E) (Q : Finset E) :
    (∑ e ∈ Q, a e * (load A e : ℝ)) ^ 2 ≤
      (∑ e ∈ Q, a e) * sumCost G A := by
  have hS : ∑ e ∈ Q, a e * (load A e : ℝ) ^ 2 ≤ sumCost G A := by
    rw [sumCost_eq]
    calc ∑ e ∈ Q, a e * (load A e : ℝ) ^ 2
        ≤ ∑ e ∈ Q, (load A e : ℝ) * G.latency e (load A e) := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [hlat]
          nlinarith [hb e, (Nat.cast_nonneg (load A e) : (0 : ℝ) ≤ load A e)]
      _ ≤ ∑ e, (load A e : ℝ) * G.latency e (load A e) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun e _ _ => ?_
          rw [hlat]
          have := ha e
          have := hb e
          have : (0 : ℝ) ≤ load A e := Nat.cast_nonneg _
          positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Q (fun e => Real.sqrt (a e))
    (fun e => Real.sqrt (a e) * (load A e : ℝ))
  have e1 : ∀ e, Real.sqrt (a e) * (Real.sqrt (a e) * (load A e : ℝ)) = a e * load A e := by
    intro e
    rw [← mul_assoc, Real.mul_self_sqrt (ha e)]
  have e2 : ∀ e, Real.sqrt (a e) ^ 2 = a e := fun e => Real.sq_sqrt (ha e)
  have e3 : ∀ e, (Real.sqrt (a e) * (load A e : ℝ)) ^ 2 = a e * (load A e : ℝ) ^ 2 := by
    intro e
    rw [mul_pow, e2]
  simp only [e1, e2, e3] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left hS (Finset.sum_nonneg fun e _ => ha e))

