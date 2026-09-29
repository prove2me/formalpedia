-- Prove2me | solution 1 for FirstOrderOpt.Stochastic.stochastic_mirror_iterate_three_point
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:41:03.492891+00:00
-- url     : https://prove2.me/submissions/64ba6b34-0f52-4849-9916-4106078e6aff

import Mathlib

namespace FirstOrderOpt.Stochastic

end FirstOrderOpt.Stochastic

open FirstOrderOpt.Stochastic

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (V : E → E → ℝ) (xt xt1 : E) (Gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * Gt xt1 + V xt xt1 ≤ γt * Gt x + V xt x),
    ∀ x ∈ X, γt * Gt (xt1 - x) + V xt xt1 ≤ V xt x - V xt1 x) := by
  intro h
  have := h (E := ℝ) Set.univ (fun _ _ => 1) 0 0 0 0 (Set.mem_univ _)
    (fun x _ => by simp) 0 (Set.mem_univ _)
  norm_num at this
