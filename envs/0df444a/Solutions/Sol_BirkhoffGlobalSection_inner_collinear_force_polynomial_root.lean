-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_collinear_force_polynomial_root
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:41:38.359034+00:00
-- url     : https://prove2.me/submissions/6c46e253-e216-473a-812d-215bb2279edf

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    ∃ x : ℝ, -μ < x ∧ x < 1 - μ ∧
      x * (x + μ) ^ 2 * (1 - μ - x) ^ 2 -
        (1 - μ) * (1 - μ - x) ^ 2 + μ * (x + μ) ^ 2 = 0 := by
  let P : ℝ → ℝ := fun x =>
    x * (x + μ) ^ 2 * (1 - μ - x) ^ 2 -
      (1 - μ) * (1 - μ - x) ^ 2 + μ * (x + μ) ^ 2
  have hcont : Continuous P := by dsimp [P]; fun_prop
  have hleftval : P (-μ) = -(1 - μ) := by dsimp [P]; ring
  have hrightval : P (1 - μ) = μ := by dsimp [P]; ring
  have hleftneg : P (-μ) < 0 := by rw [hleftval]; linarith
  have hrightpos : 0 < P (1 - μ) := by rw [hrightval]; exact hμ0
  have hle : -μ ≤ 1 - μ := by linarith
  have hzero_mem : (0 : ℝ) ∈ P '' Set.Icc (-μ) (1 - μ) :=
    intermediate_value_Icc hle hcont.continuousOn
      ⟨le_of_lt hleftneg, le_of_lt hrightpos⟩
  rcases hzero_mem with ⟨x, ⟨hxlo, hxhi⟩, hzero⟩
  have hxlo' : -μ < x := by
    rcases lt_or_eq_of_le hxlo with h | h
    · exact h
    · exfalso
      rw [← h] at hzero
      linarith
  have hxhi' : x < 1 - μ := by
    rcases lt_or_eq_of_le hxhi with h | h
    · exact h
    · exfalso
      rw [h] at hzero
      linarith
  exact ⟨x, hxlo', hxhi', hzero⟩
