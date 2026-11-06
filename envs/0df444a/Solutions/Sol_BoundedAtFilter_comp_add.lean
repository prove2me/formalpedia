-- Prove2me | solution 1 for BoundedAtFilter.comp_add
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:28:04.004684+00:00
-- url     : https://prove2.me/submissions/d103a953-009b-48f4-85ce-2a7194e120d5

import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

set_option autoImplicit false

theorem solution {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  constructor
  · intro h
    have ht : Tendsto (fun n : ℕ => n - N) atTop atTop := by
      refine tendsto_atTop.2 fun b => eventually_atTop.2 ⟨b + N, fun n hn => by omega⟩
    refine (h.comp_tendsto ht).congr' ?_ (by simp)
    filter_upwards [eventually_ge_atTop N] with n hn
    dsimp
    congr 1
    omega
  · intro h
    have ht : Tendsto (fun n : ℕ => n + N) atTop atTop := by
      refine tendsto_atTop.2 fun b => eventually_atTop.2 ⟨b, fun n hn => by omega⟩
    exact h.comp_tendsto ht
