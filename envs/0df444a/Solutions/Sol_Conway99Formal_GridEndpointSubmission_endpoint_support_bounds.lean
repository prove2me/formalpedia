-- Prove2me | solution 1 for Conway99Formal.GridEndpointSubmission.endpoint_support_bounds
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:39:18.223984+00:00
-- url     : https://prove2.me/submissions/19aa9a14-cf2a-4a42-a1ec-382bf5ec4f66

import Mathlib
import Definitions.Def_grid_endpoint_data

set_option autoImplicit false
open Finset SimpleGraph

namespace Conway99Formal.GridEndpointSubmission

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (D : Conway99Formal.GridEndpoint.EndpointData G) :
    33 ≤ D.ordinary ∧ D.ordinary ≤ 50 ∧
      49 ≤ 99 - D.ordinary ∧ 99 - D.ordinary ≤ 66 := by
  classical
  let zeroSet : Finset V := Finset.univ.filter fun u => D.traceDefect u = 0
  have hsplit : D.ordinary +
      (Finset.univ.filter fun u => D.traceDefect u ≠ 0).card = 99 := by
    rw [D.ordinary_correct]
    simpa [D.srg.card] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (p := fun u => D.traceDefect u = 0))
  have hpositive :
      (Finset.univ.filter fun u => D.traceDefect u ≠ 0).card ≤
        ∑ u : V, D.traceDefect u := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro u _
    by_cases hz : D.traceDefect u = 0
    · simp [hz]
    · simp only [if_pos hz]
      omega
  have hordinary_lower : 33 ≤ D.ordinary := by
    rw [D.trace_budget] at hpositive
    omega
  have hleft : 7 * zeroSet.card =
      ∑ u ∈ zeroSet, ((Conway99Formal.GridEndpoint.trianglesOf G).filter
        fun T => u ∈ T).card := by
    calc
      7 * zeroSet.card = ∑ _u ∈ zeroSet, (7 : ℕ) := by simp [mul_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        exact (D.ordinary_seven u (Finset.mem_filter.mp hu).2).symm
  have hswap :
      (∑ u ∈ zeroSet, ((Conway99Formal.GridEndpoint.trianglesOf G).filter
        fun T => u ∈ T).card) =
      ∑ T ∈ Conway99Formal.GridEndpoint.trianglesOf G, (T ∩ zeroSet).card := by
    calc
      _ = ∑ u ∈ zeroSet, ∑ T ∈ Conway99Formal.GridEndpoint.trianglesOf G,
          if u ∈ T then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact Finset.card_filter (fun T => u ∈ T)
          (Conway99Formal.GridEndpoint.trianglesOf G)
      _ = ∑ T ∈ Conway99Formal.GridEndpoint.trianglesOf G,
          ∑ u ∈ zeroSet, if u ∈ T then 1 else 0 := by rw [Finset.sum_comm]
      _ = ∑ T ∈ Conway99Formal.GridEndpoint.trianglesOf G, (T ∩ zeroSet).card := by
        apply Finset.sum_congr rfl
        intro T hT
        calc
          (∑ u ∈ zeroSet, if u ∈ T then 1 else 0) =
              (zeroSet.filter fun u => u ∈ T).card := by rw [Finset.card_filter]
          _ = (T ∩ zeroSet).card := by
            congr 1
            ext u
            simp [Finset.mem_inter, and_comm]
  have hbound : (∑ T ∈ Conway99Formal.GridEndpoint.trianglesOf G,
      (T ∩ zeroSet).card) ≤
      ∑ T ∈ Conway99Formal.GridEndpoint.trianglesOf G,
        (if Conway99Formal.GridEndpoint.prismDegree G T = 10 then 2 else
          if Conway99Formal.GridEndpoint.prismDegree G T = 12 then 3 else 0) := by
    apply Finset.sum_le_sum
    intro T hT
    exact D.triangle_ordinary_cap T hT
  have hsplit_prism (T : Finset V) :
      (if Conway99Formal.GridEndpoint.prismDegree G T = 10 then 2 else
        if Conway99Formal.GridEndpoint.prismDegree G T = 12 then 3 else 0) =
      (if Conway99Formal.GridEndpoint.prismDegree G T = 10 then 2 else 0) +
      (if Conway99Formal.GridEndpoint.prismDegree G T = 12 then 3 else 0) := by
    split_ifs <;> omega
  have hinc : 7 * D.ordinary ≤ 2 * D.n10 + 3 * D.n12 := by
    have hinc' : 7 * zeroSet.card ≤
        2 * ((Conway99Formal.GridEndpoint.trianglesOf G).filter fun T =>
          Conway99Formal.GridEndpoint.prismDegree G T = 10).card +
        3 * ((Conway99Formal.GridEndpoint.trianglesOf G).filter fun T =>
          Conway99Formal.GridEndpoint.prismDegree G T = 12).card := by
      calc
        7 * zeroSet.card =
            ∑ T ∈ Conway99Formal.GridEndpoint.trianglesOf G, (T ∩ zeroSet).card :=
          hleft.trans hswap
        _ ≤ _ := hbound
        _ = _ := by
          simp_rw [hsplit_prism]
          simp [Finset.sum_add_distrib, Finset.sum_ite, mul_comm]
    change 7 * (Finset.univ.filter fun u => D.traceDefect u = 0).card ≤
      2 * ((Conway99Formal.GridEndpoint.trianglesOf G).filter fun T =>
        Conway99Formal.GridEndpoint.prismDegree G T = 10).card +
      3 * ((Conway99Formal.GridEndpoint.trianglesOf G).filter fun T =>
        Conway99Formal.GridEndpoint.prismDegree G T = 12).card at hinc'
    rw [← D.ordinary_correct, ← D.n10_correct, ← D.n12_correct] at hinc'
    exact hinc'
  have hcensus := D.triangle_count
  have hprismsum := D.prism_sum
  omega

end Conway99Formal.GridEndpointSubmission

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (D : Conway99Formal.GridEndpoint.EndpointData G) : 33 ≤ D.ordinary ∧ D.ordinary ≤ 50 ∧ 49 ≤ 99 - D.ordinary ∧ 99 - D.ordinary ≤ 66 := by
  exact Conway99Formal.GridEndpointSubmission.solution D

#print axioms solution
