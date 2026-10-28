-- Prove2me | solution 1 for FunctionalInequalities.Analysis.opNorm_sq_le_hsNormSq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:49.669766+00:00
-- url     : https://prove2.me/submissions/80c1d527-b408-4266-aeee-01ed31e4e7cf

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Theorems.Thm_FunctionalInequalities_Analysis_norm_apply_sq_le_hsNormSq_mul_readable

noncomputable section
open scoped RealInnerProductSpace
variable {n : ℕ}
theorem FunctionalInequalities.Analysis.hsNormSq_nonneg (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : 0 ≤ hsNormSq M := by
  unfold hsNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
/-- The operator norm is dominated by the Hilbert–Schmidt norm. -/
theorem solution (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖M‖ ^ 2 ≤ FunctionalInequalities.Analysis.hsNormSq M := by
  have hbound : ‖M‖ ≤ Real.sqrt (FunctionalInequalities.Analysis.hsNormSq M) := by
    apply M.opNorm_le_bound (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    calc
      ‖M x‖ ^ 2 ≤ FunctionalInequalities.Analysis.hsNormSq M * ‖x‖ ^ 2 :=
        FunctionalInequalities.Analysis.norm_apply_sq_le_hsNormSq_mul_readable M x
      _ = (Real.sqrt (FunctionalInequalities.Analysis.hsNormSq M) * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (FunctionalInequalities.Analysis.hsNormSq_nonneg M)]
  calc
    ‖M‖ ^ 2 ≤ Real.sqrt (FunctionalInequalities.Analysis.hsNormSq M) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = FunctionalInequalities.Analysis.hsNormSq M := Real.sq_sqrt (FunctionalInequalities.Analysis.hsNormSq_nonneg M)
