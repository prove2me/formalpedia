-- Prove2me | solution 1 for DiscreteConvex.CombinatorialC.prop_2_27_optimal_perturbation_pair
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:45:53.3963+00:00
-- url     : https://prove2.me/submissions/2bf0aa84-ec78-42ca-8b14-94b9af3c7484

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsOptimalCirc
import Definitions.Def_DiscreteConvex_CombinatorialC_CharVec

set_option autoImplicit false

namespace CexF0e0fa05
open DiscreteConvex.CombinatorialC

/-- One vertex, two self-loop arcs: every flow is a circulation. -/
theorem feas (x : Fin 2 → ℝ) (h0 : 0 ≤ x 0 ∧ x 0 ≤ 1) (h1 : 0 ≤ x 1 ∧ x 1 ≤ 1) :
    IsFeasibleCirc (V := Unit) (fun _ : Fin 2 => ()) (fun _ => ()) (fun _ => 1) x := by
  refine ⟨fun a => ?_, fun v => ?_⟩
  · fin_cases a
    · exact h0
    · exact h1
  · simp [Boundary]

theorem opt_half : IsOptimalCirc (V := Unit) (fun _ : Fin 2 => ()) (fun _ => ()) 0 (fun _ => 1)
    (fun _ => 1 / 2) := by
  refine ⟨feas _ (by norm_num) (by norm_num), fun xi' _ => ?_⟩
  simp

end CexF0e0fa05

open DiscreteConvex.CombinatorialC in
theorem solution : ¬ (∀ {V A : Type} [Fintype A] [Fintype V]
    [DecidableEq V] [DecidableEq A] (src dst : A → V) (S : Finset A) (w1 w2 c : A → ℝ) (a : A)
    (xi1 xi2 : A → ℝ) (hxi1 : IsOptimalCirc src dst w1 c xi1)
    (hxi2 : IsOptimalCirc src dst w2 c xi2),
    ∃ α0 : ℝ, 0 < α0 ∧ ∀ b ∈ S.erase a, ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      IsOptimalCirc src dst (w1 - α • (CharVec a - CharVec b)) c xi1 ∧
        IsOptimalCirc src dst (w2 + α • (CharVec a - CharVec b)) c xi2) := by
  intro h
  obtain ⟨α0, hα0, hall⟩ := h (V := Unit) (A := Fin 2) (fun _ => ()) (fun _ => ())
    Finset.univ 0 0 (fun _ => 1) 0 (fun _ => 1 / 2) (fun _ => 1 / 2)
    CexF0e0fa05.opt_half CexF0e0fa05.opt_half
  have hb : (1 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)).erase 0 := by decide
  have key := (hall 1 hb α0 hα0.le le_rfl).1.2 ![0, 1]
    (CexF0e0fa05.feas _ (by simp) (by simp))
  simp [dotProduct, Fin.sum_univ_two, CharVec] at key
  linarith
