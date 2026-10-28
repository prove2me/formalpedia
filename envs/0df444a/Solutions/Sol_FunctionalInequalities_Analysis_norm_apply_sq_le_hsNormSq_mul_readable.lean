-- Prove2me | solution 1 for FunctionalInequalities.Analysis.norm_apply_sq_le_hsNormSq_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:40:53.751565+00:00
-- url     : https://prove2.me/submissions/62db8709-c793-439e-b2f7-0e55845c3c2a

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
/-- `‖M x‖² ≤ ‖M‖²_HS ‖x‖²`. -/
theorem solution (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ‖M x‖ ^ 2 ≤ FunctionalInequalities.Analysis.hsNormSq M * ‖x‖ ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hx : (∑ j, ⟪b j, x⟫ • b j) = x := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_repr x
  have hMx : M x = ∑ j, ⟪b j, x⟫ • M (b j) := by
    calc
      M x = M (∑ j, ⟪b j, x⟫ • b j) := congrArg M hx.symm
      _ = ∑ j, ⟪b j, x⟫ • M (b j) := by
        simp only [map_sum, map_smul]
  have hnorm : ‖M x‖ ≤ ∑ j, |⟪b j, x⟫| * ‖M (b j)‖ := by
    calc
      ‖M x‖ = ‖∑ j, ⟪b j, x⟫ • M (b j)‖ := congrArg norm hMx
      _ ≤ ∑ j, ‖⟪b j, x⟫ • M (b j)‖ :=
        norm_sum_le Finset.univ _
      _ = ∑ j, |⟪b j, x⟫| * ‖M (b j)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
  have hCS :
      (∑ j, |⟪b j, x⟫| * ‖M (b j)‖) ^ 2 ≤
        ‖x‖ ^ 2 * FunctionalInequalities.Analysis.hsNormSq M := by
    simpa only [sq_abs, b, FunctionalInequalities.Analysis.basis_sum_inner_sq, ← FunctionalInequalities.Analysis.hsNormSq_eq_sum_norm_sq] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => |⟪b j, x⟫|) (fun j => ‖M (b j)‖))
  calc
    ‖M x‖ ^ 2 ≤ (∑ j, |⟪b j, x⟫| * ‖M (b j)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ ‖x‖ ^ 2 * FunctionalInequalities.Analysis.hsNormSq M := hCS
    _ = FunctionalInequalities.Analysis.hsNormSq M * ‖x‖ ^ 2 := mul_comm _ _
