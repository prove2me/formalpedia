-- Prove2me | solution 1 for FunctionalInequalities.Analysis.centeredDifference_nonneg_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:05:38.236841+00:00
-- url     : https://prove2.me/submissions/740a6b6b-e1a0-4c27-aba5-793d08e25f20

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open scoped RealInnerProductSpace
section CenteredDifference
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
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
