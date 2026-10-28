-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integrable_inv_hessianMatrix_mul_of_bounded_compact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:09.156422+00:00
-- url     : https://prove2.me/submissions/e7999779-770f-49af-88b8-7b44a4f6ccc4

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Piola

noncomputable section
open Matrix
open FunctionalInequalities.Probability.Stein
section LN10AInverseHessianDivergence
open MeasureTheory Set Filter
open scoped Topology
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
private lemma FunctionalInequalities.Analysis.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Analysis.n10_matrix (fderiv ℝ (gradient u) x) := by
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
private lemma FunctionalInequalities.Analysis.n10_continuous_cofactor {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        (FunctionalInequalities.Analysis.n10_matrix L).adjugate i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  apply (continuous_apply j).comp
  apply (continuous_apply i).comp
  apply Continuous.matrix_adjugate
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const
private lemma FunctionalInequalities.Analysis.n10_measurable_cofactor {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => (hessianMatrix u x).adjugate i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n10_continuous_cofactor i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))
private lemma FunctionalInequalities.Analysis.n10_cofactor_bound {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n) :
    ∃ C : ℝ, ∀ x, ‖(hessianMatrix u x).adjugate i j‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (G : ℝ)).exists_bound_of_continuousOn
        (n10_continuous_cofactor i j).continuousOn
  refine ⟨C, fun x => ?_⟩
  rw [n10_hessian]
  apply hC
  change dist (fderiv ℝ (gradient u) x) 0 ≤ (G : ℝ)
  rw [dist_zero_right]
  exact norm_fderiv_le_of_lipschitz ℝ hG
end StructuredSpace
/-- Compactly supported bounded multipliers are integrable against inverse-Hessian
entries under the existing weak Monge-Ampere assumptions for Letwin (2.2). -/
theorem solution {n : ℕ}
    {u F f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : NNReal} (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (F x))
    (hf : Measurable f) (hfc : HasCompactSupport f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (i j : Fin n) :
    Integrable (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hw : Continuous (fun x => Real.exp (-F x)) :=
    Real.continuous_exp.comp hF.neg
  -- The bounded-compact argument of `n10_integrable_bounded_compact`,
  -- with continuous multiplication as in `n10_integrable_weighted_deriv`.
  have hl : LocallyIntegrable f
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_top_of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)).locallyIntegrable le_top
  have hwl := LocallyIntegrable.continuous_mul hw hl
  have hwi : Integrable (fun x => Real.exp (-F x) * f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply (hwl.integrableOn_isCompact hfc.isCompact).integrable_of_forall_notMem_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  obtain ⟨B, hB⟩ := FunctionalInequalities.Analysis.n10_cofactor_bound hG i j
  have hi := hwi.bdd_mul
    (FunctionalInequalities.Analysis.n10_measurable_cofactor u i j).aestronglyMeasurable
    (Filter.Eventually.of_forall hB)
  -- The AE inverse representation and congruence argument of
  -- `sum_integral_inv_hessianMatrix_mul_fderiv_eq` above.
  have hinv :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j =
          Real.exp (-F x) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j := by
    filter_upwards [hdet] with x hx
    simp only [Matrix.inv_def, hx, Ring.inverse_eq_inv, Matrix.smul_apply,
      smul_eq_mul, Real.exp_neg]
  apply hi.congr
  filter_upwards [hinv] with x hx
  change (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j * (Real.exp (-F x) * f x) =
    (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * f x
  rw [hx]
  ring
