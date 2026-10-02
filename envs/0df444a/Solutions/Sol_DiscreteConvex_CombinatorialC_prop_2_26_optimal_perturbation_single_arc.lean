-- Prove2me | solution 1 for DiscreteConvex.CombinatorialC.prop_2_26_optimal_perturbation_single_arc
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:38:44.04799+00:00
-- url     : https://prove2.me/submissions/f6f0fca3-80b0-41d2-9b21-246984812aff

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsOptimalCirc
import Definitions.Def_DiscreteConvex_CombinatorialC_CharVec

section Helpersb8
open DiscreteConvex.CombinatorialC

/-- On a single self-loop with capacity 1, every value in `[0,1]` is a feasible circulation. -/
theorem feas_loop_b8 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IsFeasibleCirc (fun _ : Unit => ()) (fun _ : Unit => ()) (1 : Unit → ℝ) (fun _ => t) := by
  refine ⟨fun _ => ⟨h0, by simpa using h1⟩, fun v => ?_⟩
  simp [Boundary]

/-- With weight 0 the full flow `1` on the self-loop is optimal. -/
theorem opt_loop_b8 :
    IsOptimalCirc (fun _ : Unit => ()) (fun _ : Unit => ()) (0 : Unit → ℝ) (1 : Unit → ℝ)
      (1 : Unit → ℝ) := by
  refine ⟨feas_loop_b8 1 zero_le_one le_rfl, fun xi' _ => ?_⟩
  simp

end Helpersb8

open DiscreteConvex.CombinatorialC in
theorem solution : ¬ (∀ {V A : Type} [Fintype A] [Fintype V]
    [DecidableEq V] [DecidableEq A] (src dst : A → V) (w1 w2 c : A → ℝ) (a : A)
    (xi1 xi2 : A → ℝ) (hxi1 : IsOptimalCirc src dst w1 c xi1)
    (hxi2 : IsOptimalCirc src dst w2 c xi2),
    ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      IsOptimalCirc src dst (w1 - α • CharVec a) c xi1 ∧
        IsOptimalCirc src dst (w2 + α • CharVec a) c xi2) := by
  intro h
  obtain ⟨α0, hα0, hall⟩ := h (fun _ : Unit => ()) (fun _ : Unit => ()) 0 0 1 () 1 1
    opt_loop_b8 opt_loop_b8
  have key := (hall α0 hα0.le le_rfl).1.2 (fun _ => 0) (feas_loop_b8 0 le_rfl zero_le_one)
  simp [dotProduct, CharVec] at key
  linarith
