-- Prove2me | solution 1 for FunctionalInequalities.Analysis.sum_inner_apply_le_sqrt_hsNormSq_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:04.210292+00:00
-- url     : https://prove2.me/submissions/4571c900-71da-4869-b07c-8b438d12fadd

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt

noncomputable section
open scoped RealInnerProductSpace
variable {n : ℕ}
private theorem FunctionalInequalities.Analysis.basis_sum_inner_sq (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫ ^ 2) = ‖x‖ ^ 2 := by
  calc
    (∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫ ^ 2) =
        ∑ i, ⟪x, EuclideanSpace.basisFun (Fin n) ℝ i⟫ *
          ⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm x (EuclideanSpace.basisFun (Fin n) ℝ i), pow_two]
    _ = ⟪x, x⟫ :=
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner x x
    _ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
/-- Parseval: `‖M‖²_HS = Σ_j ‖M e_j‖²`. -/
theorem FunctionalInequalities.Analysis.hsNormSq_eq_sum_norm_sq (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    hsNormSq M = ∑ j, ‖M (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2 := by
  unfold hsNormSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact basis_sum_inner_sq (M (EuclideanSpace.basisFun (Fin n) ℝ j))
/-- Cauchy–Schwarz for the Hilbert–Schmidt pairing `Σ_j ⟪M e_j, N e_j⟫`. -/
theorem solution (M N : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∑ j, ⟪M (EuclideanSpace.basisFun (Fin n) ℝ j), N (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ≤
      Real.sqrt (FunctionalInequalities.Analysis.hsNormSq M) * Real.sqrt (FunctionalInequalities.Analysis.hsNormSq N) := by
  calc
    (∑ j, ⟪M (EuclideanSpace.basisFun (Fin n) ℝ j),
        N (EuclideanSpace.basisFun (Fin n) ℝ j)⟫) ≤
        ∑ j, ‖M (EuclideanSpace.basisFun (Fin n) ℝ j)‖ *
          ‖N (EuclideanSpace.basisFun (Fin n) ℝ j)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact real_inner_le_norm _ _
    _ ≤ Real.sqrt (∑ j, ‖M (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2) *
        Real.sqrt (∑ j, ‖N (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun j => ‖M (EuclideanSpace.basisFun (Fin n) ℝ j)‖)
        (fun j => ‖N (EuclideanSpace.basisFun (Fin n) ℝ j)‖)
    _ = Real.sqrt (FunctionalInequalities.Analysis.hsNormSq M) * Real.sqrt (FunctionalInequalities.Analysis.hsNormSq N) := by
      rw [← FunctionalInequalities.Analysis.hsNormSq_eq_sum_norm_sq, ← FunctionalInequalities.Analysis.hsNormSq_eq_sum_norm_sq]
