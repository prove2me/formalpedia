-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:36:55.406874+00:00
-- url     : https://prove2.me/submissions/53333cb9-62e6-4c7d-8c54-5898570a2f60

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_QuadraticAction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Letwin_RegularClass
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Letwin_CompactBound
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_letwinCompactBound_of_regularClass_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_regularClass_matrix_variance_le_eight_readable

section
noncomputable section
open scoped RealInnerProductSpace MatrixOrder
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section OperatorMatrix
open Matrix
variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
@[simp] theorem FunctionalInequalities.Analysis.operatorOfMatrix_operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    operatorOfMatrix b (operatorMatrix b T) = T := by
  exact congrArg (fun f : E →ₗ[ℝ] E => f.toContinuousLinearMap)
    ((LinearMap.toMatrixOrthonormal b).symm_apply_apply T.toLinearMap)
end OperatorMatrix
end
end
end

section
noncomputable section
open scoped RealInnerProductSpace
noncomputable section
section
theorem FunctionalInequalities.Analysis.sum_inner_apply_sq_eq_trace_comp_of_isSymmetric
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (hA : (A : E →ₗ[ℝ] E).IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) :
    (∑ i, ∑ j, ⟪A (b i),b j⟫ ^ 2) = LinearMap.trace ℝ E (A.toLinearMap * A.toLinearMap) := by
  simp_rw [b.sum_sq_inner_left]
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_self_eq_norm_sq (A (b i))]
  exact hA (b i) (A (b i))
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
theorem FunctionalInequalities.Probability.Stein.quadratic_matrix_sum_eq_inner_action {n : ℕ} (A : KernelMatrix n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ∑ j, A i j*x i*x j) = ⟪action A x,x⟫ := by
  simp only [action,PiLp.inner_apply,Real.inner_apply,Matrix.mulVec,dotProduct]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end
end
end

section
section RegularSource
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ Set.univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) =
      (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
noncomputable section
open MeasureTheory ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
section
theorem FunctionalInequalities.KLS.LogConcave.letwinQuadraticBound_of_matrix_variance_bound {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (h : ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm →
      variance (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, M i j*x i*x j) μ ≤
        8*Matrix.trace (M*M)) : LetwinQuadraticBound μ := by
  let E := EuclideanSpace ℝ (Fin n)
  intro A hA
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let M : Matrix (Fin n) (Fin n) ℝ := Analysis.operatorMatrix b A
  have hMA : (Matrix.toEuclideanLin M).toContinuousLinearMap = A :=
    Analysis.operatorOfMatrix_operatorMatrix b A
  have hSym : (Matrix.toEuclideanLin M).IsSymmetric := by
    change ((Matrix.toEuclideanLin M).toContinuousLinearMap : E →ₗ[ℝ] E).IsSymmetric
    rw [hMA]
    exact hA.isSymmetric
  have hM : M.IsSymm := Matrix.isHermitian_iff_isSymm.mp
    (Matrix.isSymmetric_toEuclideanLin_iff.mp hSym)
  have hcoord (x : E) : (∑ i, ∑ j, M i j*x i*x j) = ⟪A x,x⟫ := by
    rw [quadratic_matrix_sum_eq_inner_action]
    change ⟪(Matrix.toEuclideanLin M).toContinuousLinearMap x,x⟫ = _
    rw [hMA]
  have hv : variance (fun x : E => ⟪A x,x⟫) μ ≤ 8*Matrix.trace (M*M) := by
    simpa only [hcoord] using h M hM
  have htrace : LinearMap.trace ℝ E (A.toLinearMap*A.toLinearMap) = Matrix.trace (M*M) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis,LinearMap.toMatrix_mul]
    rfl
  have hHS : (∑ i, ∑ j, ⟪A (stdOrthonormalBasis ℝ E i),stdOrthonormalBasis ℝ E j⟫^2) =
      Matrix.trace (M*M) :=
    (Analysis.sum_inner_apply_sq_eq_trace_comp_of_isSymmetric A hA.isSymmetric
      (stdOrthonormalBasis ℝ E)).trans htrace
  calc
    _ = variance (fun x : E => ⟪A x,x⟫) μ :=
      (variance_eq_integral (A.continuous.inner continuous_id).measurable.aemeasurable).symm
    _ ≤ 8*Matrix.trace (M*M) := hv
    _ = _ := by rw [hHS]
end
end
noncomputable section
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
section
include hn hκ hK hKc hKint hW hstrong hμ hiso in
theorem FunctionalInequalities.KLS.LogConcave.regularClass_letwinQuadraticBound :
    LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply letwinQuadraticBound_of_matrix_variance_bound
  exact regularClass_matrix_variance_le_eight_readable hn hκ hK hKc hKint hW hstrong μ hμ hiso
end
end
end RegularSource
end

noncomputable section
open MeasureTheory Set
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
theorem solution : FunctionalInequalities.KLS.LogConcave.Suspension.LetwinCompactBound := by
  apply FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound_of_regularClass_readable
  intro n hn K W κ hκ hK hKc hKint hW hstrong μ hμ hiso
  exact FunctionalInequalities.KLS.LogConcave.regularClass_letwinQuadraticBound hn hκ hK hKc hKint hW hstrong μ hμ hiso
