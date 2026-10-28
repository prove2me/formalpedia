-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:34.731131+00:00
-- url     : https://prove2.me/submissions/b1653390-1ebd-4137-b767-159dedd72ff9

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F2TruncatedConjugate
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- The supremum is attained and dominates every value on the ball. -/
theorem solution {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) (p : E) :
    (∃ x ∈ closedBall (0 : E) M, FunctionalInequalities.Analysis.truncatedConjugate u M p = ⟪p, x⟫ - u x) ∧
      ∀ x ∈ closedBall (0 : E) M, ⟪p, x⟫ - u x ≤ FunctionalInequalities.Analysis.truncatedConjugate u M p := by
  have hc :
      IsCompact ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M) :=
    (isCompact_closedBall (0 : E) M).image
      ((continuous_const.inner continuous_id).sub hu)
  have hn :
      ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M).Nonempty :=
    ⟨⟪p, 0⟫ - u 0, ⟨0, mem_closedBall_self hM, rfl⟩⟩
  constructor
  · obtain ⟨x, hx, heq⟩ := hc.sSup_mem hn
    exact ⟨x, hx, heq.symm⟩
  · intro x hx
    exact le_csSup hc.bddAbove ⟨x, hx, rfl⟩
