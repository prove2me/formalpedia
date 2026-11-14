-- Prove2me | solution 1 for ConsistentSubmodular.twoTypeInterpolation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:37.476514+00:00
-- url     : https://prove2.me/submissions/4c6c80b8-1e31-4053-bf7c-513e99565227

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_three_quarter_le_twoTypeValue

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

section TwoType

variable {n : ℕ} (f : Objective n) (Q A B : Finset (Fin n))

/-- Formula (23): `H_Q(A, B; s) = λ + (1 - s) a + s b - s (1 - s) o`. -/
theorem twoTypeValue_eq (s : ℝ) :
    twoTypeValue f Q A B s = f.value Q + (1 - s) * (f.value (Q ∪ A) - f.value Q) +
      s * (f.value (Q ∪ B) - f.value Q) -
      s * (1 - s) * (f.value (Q ∪ A) + f.value (Q ∪ B) - f.value (Q ∪ (A ∪ B)) - f.value Q) := by
  unfold twoTypeValue
  ring

/-- Monotonicity bounds the residual overlap by both residuals:
`o ≤ min(a, b)`. -/
theorem overlap_le :
    f.value (Q ∪ A) + f.value (Q ∪ B) - f.value (Q ∪ (A ∪ B)) - f.value Q ≤
        f.value (Q ∪ A) - f.value Q ∧
      f.value (Q ∪ A) + f.value (Q ∪ B) - f.value (Q ∪ (A ∪ B)) - f.value Q ≤
        f.value (Q ∪ B) - f.value Q := by
  have hB := f.monotone (Q ∪ B) (Q ∪ (A ∪ B)) (by
    intro e he
    simp only [Finset.mem_union] at he ⊢
    tauto)
  have hA := f.monotone (Q ∪ A) (Q ∪ (A ∪ B)) (by
    intro e he
    simp only [Finset.mem_union] at he ⊢
    tauto)
  constructor <;> linarith

/-- Inequality (24): at the midpoint,
`H_Q(A, B; 1/2) ≥ λ + (a + b)/2 - min(a, b)/4`. -/
theorem twoTypeValue_half_ge :
    f.value Q + ((f.value (Q ∪ A) - f.value Q) + (f.value (Q ∪ B) - f.value Q)) / 2 -
        min (f.value (Q ∪ A) - f.value Q) (f.value (Q ∪ B) - f.value Q) / 4 ≤
      twoTypeValue f Q A B (1 / 2) := by
  obtain ⟨hoa, hob⟩ := overlap_le f Q A B
  rw [twoTypeValue_eq]
  rcases le_total (f.value (Q ∪ A) - f.value Q) (f.value (Q ∪ B) - f.value Q) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

end TwoType

namespace WindowBounds

/-- **Lemma B.3** (two-type interpolation). -/
theorem twoTypeInterpolation : TwoTypeInterpolationGoal := by
  intro n f Q A B
  dsimp only
  exact ⟨fun s _ _ => twoTypeValue_eq f Q A B s, twoTypeValue_half_ge f Q A B,
    fun _ hwA hwB _ hs0 hs1 => three_quarter_le_twoTypeValue f Q A B hwA hwB hs0 hs1⟩

end WindowBounds

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution : TwoTypeInterpolationGoal :=
  WindowBounds.twoTypeInterpolation

end
