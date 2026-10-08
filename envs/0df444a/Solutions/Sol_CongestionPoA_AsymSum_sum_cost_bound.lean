-- Prove2me | solution 1 for CongestionPoA.AsymSum.sum_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T17:44:48.327241+00:00
-- url     : https://prove2.me/submissions/9cde6bfb-372e-486f-894e-40921d3cf0fa

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Theorems.Thm_CongestionPoA_AsymSum_nash_deviation_bound

set_option autoImplicit false

open CongestionPoA.AsymSum in
theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ ∑ i, ∑ e ∈ P i, G.latency e (load A e + 1) ∧
      ∑ i, ∑ e ∈ P i, G.latency e (load A e + 1) =
        ∑ e, (load P e : ℝ) * G.latency e (load A e + 1) := by
  constructor
  · unfold sumCost
    apply Finset.sum_le_sum
    intro i _
    exact (nash_deviation_bound G A P hlin hA hP i).1.trans
      (nash_deviation_bound G A P hlin hA hP i).2
  · calc
      _ = ∑ i, ∑ e : E, if e ∈ P i then G.latency e (load A e + 1) else 0 := by
        simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      _ = ∑ e : E, ∑ i, if e ∈ P i then G.latency e (load A e + 1) else 0 :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        simp [← Finset.sum_filter, load]
