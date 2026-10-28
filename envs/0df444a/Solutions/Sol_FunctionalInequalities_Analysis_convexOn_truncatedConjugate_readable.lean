-- Prove2me | solution 1 for FunctionalInequalities.Analysis.convexOn_truncatedConjugate_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:08.403603+00:00
-- url     : https://prove2.me/submissions/b4f28806-c1c9-40a1-88ac-0bd239157bb5

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Theorems.Thm_FunctionalInequalities_Analysis_exists_truncatedConjugate_eq_readable

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F2TruncatedConjugate
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- The truncated conjugate is convex. -/
theorem solution {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) :
    ConvexOn ℝ univ (FunctionalInequalities.Analysis.truncatedConjugate u M) := by
  refine ⟨convex_univ, ?_⟩
  intro p hp q hq a b ha hb hab
  obtain ⟨x, hx, heq⟩ :=
    (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM (a • p + b • q)).1
  have hpx := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM p).2 x hx
  have hqx := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM q).2 x hx
  change FunctionalInequalities.Analysis.truncatedConjugate u M (a • p + b • q) ≤
    a * FunctionalInequalities.Analysis.truncatedConjugate u M p + b * FunctionalInequalities.Analysis.truncatedConjugate u M q
  rw [heq]
  calc
    ⟪a • p + b • q, x⟫ - u x =
        a * (⟪p, x⟫ - u x) + b * (⟪q, x⟫ - u x) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      nlinarith [congrArg (fun t : ℝ => t * u x) hab]
    _ ≤ a * FunctionalInequalities.Analysis.truncatedConjugate u M p + b * FunctionalInequalities.Analysis.truncatedConjugate u M q :=
      add_le_add (mul_le_mul_of_nonneg_left hpx ha)
        (mul_le_mul_of_nonneg_left hqx hb)
