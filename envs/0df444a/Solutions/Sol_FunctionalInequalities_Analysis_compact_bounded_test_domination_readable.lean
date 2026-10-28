-- Prove2me | solution 1 for FunctionalInequalities.Analysis.compact_bounded_test_domination_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:31.317552+00:00
-- url     : https://prove2.me/submissions/a1d66aab-141e-4050-9347-76811459646e

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section BoundedWeakDerivativeTesting
open MeasureTheory Filter Set
open scoped Topology ContDiff
/-- A compact-local L1 density admits a common integrable bound for rough bounded tests. -/
theorem solution {n : ℕ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {C : ℝ} (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hS : IsCompact S)
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hsupp : Function.support η ⊆ S) (hbound : ∀ x, ‖η x‖ ≤ C) :
    Integrable (S.indicator fun x => C * ‖F x‖)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ x, ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x) ∧
      Integrable (fun x => F x * η x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hb : Integrable (S.indicator fun x => C * ‖F x‖)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_indicator_iff hS.measurableSet).2
      ((hF.integrableOn_isCompact hS).norm.const_mul C)
  have hprod (x : EuclideanSpace ℝ (Fin n)) :
      ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, norm_mul]
      calc
        ‖F x‖ * ‖η x‖ ≤ ‖F x‖ * C :=
          mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)
        _ = C * ‖F x‖ := mul_comm _ _
    · have hzero : η x = 0 := by
        by_contra hne
        exact hx (hsupp hne)
      rw [Set.indicator_of_notMem hx, hzero, mul_zero, norm_zero]
  exact ⟨hb, hprod, hb.mono' (hF.aestronglyMeasurable.mul hη)
    (Filter.Eventually.of_forall hprod)⟩
