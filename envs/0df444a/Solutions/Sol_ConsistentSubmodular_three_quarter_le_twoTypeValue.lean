-- Prove2me | solution 1 for ConsistentSubmodular.three_quarter_le_twoTypeValue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:21.586205+00:00
-- url     : https://prove2.me/submissions/52377bec-f3f4-4254-8f33-21dd5be64481

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

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

end TwoType

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ} (f : Objective n) (Q A B : Finset (Fin n))

theorem solution {w : ℝ} (hwA : w ≤ f.value (Q ∪ A))
    (hwB : w ≤ f.value (Q ∪ B)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    3 / 4 * w ≤ twoTypeValue f Q A B s := by
  obtain ⟨hoa, hob⟩ := overlap_le f Q A B
  have hA := f.monotone Q (Q ∪ A) Finset.subset_union_left
  have hB := f.monotone Q (Q ∪ B) Finset.subset_union_left
  have hlam := f.nonnegative Q
  have hq0 : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
  have hq : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  rw [twoTypeValue_eq]
  -- With `v = min(a, b)`, the value is at least `λ + (1 - s(1 - s)) v ≥ λ + 3v/4`.
  rcases le_total (f.value (Q ∪ A)) (f.value (Q ∪ B)) with h | h
  · nlinarith [mul_le_mul_of_nonneg_left hoa hq0, mul_nonneg hs0 (sub_nonneg.mpr h),
      mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hA)]
  · nlinarith [mul_le_mul_of_nonneg_left hob hq0, mul_nonneg (show 0 ≤ 1 - s by linarith)
      (sub_nonneg.mpr h), mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hB)]

end
