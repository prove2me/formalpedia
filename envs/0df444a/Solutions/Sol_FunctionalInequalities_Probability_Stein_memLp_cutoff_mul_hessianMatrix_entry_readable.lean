-- Prove2me | solution 1 for FunctionalInequalities.Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:05.910615+00:00
-- url     : https://prove2.me/submissions/2d7322b5-e0d1-4b89-a15a-0de270f74149

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section HessianEntryBounds
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
section
private lemma FunctionalInequalities.Probability.Stein.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Probability.Stein.n10_matrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd :
      fderiv ℝ (fderiv ℝ u) x =
        T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl
private lemma FunctionalInequalities.Probability.Stein.n11b_continuous_hessian_entry {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        FunctionalInequalities.Probability.Stein.n10_matrix L i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const
/-- Measurability of the total coordinate Hessian, without smoothness premises. -/
theorem FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => hessianMatrix u x i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n11b_continuous_hessian_entry i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))
end
end HessianEntryBounds
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
/-- Multiplying a total Hessian entry by a continuous compact cutoff produces
an actual global L2 function for the existing difference-quotient criterion. -/
theorem solution {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    MemLp (fun x => χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hK : IsCompact (tsupport χ) := hχc
  have hKm : MeasurableSet (tsupport χ) :=
    (isClosed_tsupport χ).measurableSet
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hχ.continuousOn
  let : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hlocal : MemLp (fun x => χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)) := by
    apply MemLp.of_bound
      (hχ.measurable.mul
        (FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry u i j)).aestronglyMeasurable
      (C * (G : ℝ))
    exact (ae_restrict_mem hKm).mono fun x hx => by
      calc
        ‖χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ =
            ‖χ x‖ * ‖FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ := norm_mul _ _
        _ ≤ ‖χ x‖ * (G : ℝ) :=
          mul_le_mul_of_nonneg_left
            (FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable hG x i j)
            (norm_nonneg _)
        _ ≤ C * (G : ℝ) :=
          mul_le_mul_of_nonneg_right (hC x hx) (NNReal.coe_nonneg G)
  have heq :
      (tsupport χ).indicator (fun x => χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) =
        (fun x => χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [← heq]
  exact (memLp_indicator_iff_restrict hKm).mpr hlocal
