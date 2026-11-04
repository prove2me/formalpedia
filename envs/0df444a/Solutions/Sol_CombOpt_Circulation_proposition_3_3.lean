-- Prove2me | solution 1 for CombOpt.Circulation.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @hwr
-- created : 2026-11-03T16:59:03.255195+00:00
-- url     : https://prove2.me/submissions/34d174cc-08ce-4ccd-8fd0-5ef8810e0214

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_delta
import Definitions.Def_CombOpt_Circulation_excess
import Definitions.Def_CombOpt_Circulation_IsFlow

open CombOpt.Circulation Finset

/-- Summing an arc quantity over the arcs whose endpoint `f e` lies in `S`, grouped by vertex. -/
theorem sum_fiber_filter_eq {V E : Type*} [Fintype E] [DecidableEq V]
    (f : E → V) (S : Finset V) (x : E → ℝ) :
    ∑ v ∈ S, ∑ e ∈ univ.filter (fun e => f e = v), x e
      = ∑ e, if f e ∈ S then x e else 0 := by
  simp only [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_ite_eq]

theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : MultiDigraph V E) {r s : V} {R : Finset V} (hr : r ∈ R) (hs : s ∉ R)
    {x : E → ℝ} (hx : IsFlow G r s x) :
    ∑ e ∈ delta G R, x e - ∑ e ∈ delta G Rᶜ, x e = excess G x s := by
  -- 1. Every node of `Rᶜ` other than `s` has zero excess, so the excesses over `Rᶜ` sum to `f_x(s)`.
  have h1 : ∑ v ∈ Rᶜ, excess G x v = excess G x s := by
    rw [sum_eq_single_of_mem s (by simpa using hs)]
    intro v hv hvs
    exact hx v (fun h => by subst h; simp [hr] at hv) hvs
  -- 2. Arcs with both ends on one side cancel; what remains is `x(δ(R)) − x(δ(R̄))`.
  rw [← h1]
  unfold excess delta
  rw [sum_sub_distrib, sum_fiber_filter_eq, sum_fiber_filter_eq, sum_filter, sum_filter,
    ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  by_cases ht : G.tail e ∈ R <;> by_cases hh : G.head e ∈ R <;> simp [ht, hh]
