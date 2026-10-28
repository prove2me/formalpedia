-- Prove2me | solution 1 for FunctionalInequalities.Analysis.centeredDifference_nonneg_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:51.535449+00:00
-- url     : https://prove2.me/submissions/83130a31-b32b-448c-9c42-c24dd1e503a5

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondDifference

noncomputable section
open scoped RealInnerProductSpace
section CenteredDifference
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
/-- The centered difference bounds required by the Hessian-increment
energy estimate, with no differentiability or sign assumption on D. -/
theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u)
    {D : ℝ} (h : EuclideanSpace ℝ (Fin n))
    (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    (∀ x, 0 ≤ u (x + h) + u (x - h) - 2 * u x ∧
      u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) ∧
      0 ≤ D * ‖h‖ ^ 2 := by
  have hlower : ∀ x, 0 ≤ u (x + h) + u (x - h) - 2 * u x := by
    intro x
    have hmid :
        (1 / 2 : ℝ) • (x + h) + (1 / 2 : ℝ) • (x - h) = x := by
      apply PiLp.ext
      intro i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [← mul_add, add_add_sub_cancel, ← two_mul, ← mul_assoc]
      norm_num
    have hj :=
      hconv.2 (mem_univ (x + h)) (mem_univ (x - h))
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)
    simp only [hmid, smul_eq_mul] at hj
    apply sub_nonneg.mpr
    calc
      2 * u x = u x + u x := two_mul (u x)
      _ ≤ ((1 / 2 : ℝ) * u (x + h) + (1 / 2 : ℝ) * u (x - h)) +
          ((1 / 2 : ℝ) * u (x + h) + (1 / 2 : ℝ) * u (x - h)) :=
        add_le_add hj hj
      _ = u (x + h) + u (x - h) := by
        rw [add_add_add_comm, ← add_mul, ← add_mul]
        norm_num
  exact ⟨fun x => ⟨hlower x, hw x⟩,
    le_trans (hlower (0 : EuclideanSpace ℝ (Fin n))) (hw 0)⟩
