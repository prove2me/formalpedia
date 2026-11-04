-- Prove2me | solution 1 for CombOpt.Circulation.corollary_3_4
-- status  : ACCEPTED   (prove)
-- author  : @hwr
-- created : 2026-11-03T16:59:12.758734+00:00
-- url     : https://prove2.me/submissions/b7dde8ba-d0f8-44d8-ba70-437c5a4b93a8

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_delta
import Definitions.Def_CombOpt_Circulation_excess
import Definitions.Def_CombOpt_Circulation_IsFeasibleFlow

open CombOpt.Circulation Finset
open scoped ENNReal

/-- Summing an arc quantity over the arcs whose endpoint `f e` lies in `S`, grouped by vertex. -/
theorem sum_fiber_filter_eq {V E : Type*} [Fintype E] [DecidableEq V]
    (f : E → V) (S : Finset V) (x : E → ℝ) :
    ∑ v ∈ S, ∑ e ∈ univ.filter (fun e => f e = v), x e
      = ∑ e, if f e ∈ S then x e else 0 := by
  simp only [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_ite_eq]

/-- Flow across a cut (Proposition 3.3): `x(δ(R)) − x(δ(R̄)) = f_x(s)`. -/
theorem flow_across_cut {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : MultiDigraph V E) {r s : V} {R : Finset V} (hr : r ∈ R) (hs : s ∉ R)
    {x : E → ℝ} (hx : IsFlow G r s x) :
    ∑ e ∈ delta G R, x e - ∑ e ∈ delta G Rᶜ, x e = excess G x s := by
  have h1 : ∑ v ∈ Rᶜ, excess G x v = excess G x s := by
    rw [sum_eq_single_of_mem s (by simpa using hs)]
    intro v hv hvs
    exact hx v (fun h => by subst h; simp [hr] at hv) hvs
  rw [← h1]
  unfold excess delta
  rw [sum_sub_distrib, sum_fiber_filter_eq, sum_fiber_filter_eq, sum_filter, sum_filter,
    ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  by_cases ht : G.tail e ∈ R <;> by_cases hh : G.head e ∈ R <;> simp [ht, hh]

theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : MultiDigraph V E) (u : E → ℝ≥0∞) {r s : V} {R : Finset V}
    (hr : r ∈ R) (hs : s ∉ R) {x : E → ℝ} (hx : IsFeasibleFlow G u r s x) :
    (excess G x s : EReal) ≤ ((∑ e ∈ delta G R, u e : ℝ≥0∞) : EReal) := by
  -- 1. If the cut has infinite capacity there is nothing to show.
  by_cases htop : ∑ e ∈ delta G R, u e = ⊤
  · rw [htop]; exact le_top
  have hfin : ∀ e ∈ delta G R, u e ≠ ⊤ := fun e he =>
    (ENNReal.sum_ne_top.mp htop) e he
  -- 2. On the cut, `x e ≤ (u e).toReal`; the arcs entering `R` carry nonnegative flow.
  have hle : ∑ e ∈ delta G R, x e ≤ ∑ e ∈ delta G R, (u e).toReal := by
    refine sum_le_sum fun e he => ?_
    have h := (hx.2 e).2
    rw [← ENNReal.ofReal_toReal (hfin e he)] at h
    rw [EReal.coe_ennreal_ofReal, EReal.coe_le_coe_iff] at h
    exact h.trans (max_le le_rfl ENNReal.toReal_nonneg)
  have hin : 0 ≤ ∑ e ∈ delta G Rᶜ, x e := sum_nonneg fun e _ => (hx.2 e).1
  have hval := flow_across_cut G hr hs hx.1
  -- 3. Hence `f_x(s) ≤ u(δ(R))`, compared in `ℝ` and cast to `EReal`.
  rw [← ENNReal.ofReal_toReal htop, EReal.coe_ennreal_ofReal, EReal.coe_le_coe_iff,
    ENNReal.toReal_sum hfin]
  exact le_max_of_le_left (by linarith)
