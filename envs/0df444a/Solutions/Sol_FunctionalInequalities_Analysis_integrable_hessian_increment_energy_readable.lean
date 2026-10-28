-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integrable_hessian_increment_energy_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:03.130246+00:00
-- url     : https://prove2.me/submissions/847c6efd-771e-4830-a8cc-12cb30a542b3

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_HessianIncrement
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable

section
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
end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
/-- The squared shifted Hessian-increment density is integrable
against the continuous compact weight. No C2 or given integrability is assumed. -/
theorem solution {n : ℕ}
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (h : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => η x *
      ((∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) +
       ∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) *
      Real.exp (-u x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let w : EuclideanSpace ℝ (Fin n) → ℝ := fun x => η x * Real.exp (-u x)
  have hwc : Continuous w :=
    hη.mul (Real.continuous_exp.comp hu.neg)
  have hws : HasCompactSupport w := hηc.mul_right
  have hw : Integrable w (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hwc.integrable_of_hasCompactSupport hws
  have hentry
      (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hT : Continuous T) (i j : Fin n) :
      Integrable
        (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2 * w x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hm := FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry u i j
    have hmd :
        Measurable (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) :=
      (hm.comp hT.measurable).sub hm
    have hms :
        Measurable
          (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2) := by
      simp only [pow_two]
      exact hmd.mul hmd
    apply hw.bdd_mul hms.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    have hb :
        ‖FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ ≤
          (G : ℝ) + (G : ℝ) :=
      calc
        ‖FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ ≤
            ‖FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j‖ + ‖FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ :=
          norm_sub_le _ _
        _ ≤ (G : ℝ) + (G : ℝ) :=
          add_le_add
            (FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable hG (T x) i j)
            (FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable hG x i j)
    exact
      (norm_pow _ 2).le.trans
        (pow_le_pow_left₀ (norm_nonneg _) hb 2)
  have hsum
      (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hT : Continuous T) :
      Integrable
        (fun x => ∑ i, ∑ j,
          (FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2 * w x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hentry T hT i j
  have hp := hsum (fun x => x + h) (continuous_id.add continuous_const)
  have hm := hsum (fun x => x - h) (continuous_id.sub continuous_const)
  apply (hp.add hm).congr
  apply Filter.Eventually.of_forall
  intro x
  change
    (∑ i, ∑ j,
      (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + h) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2 * w x) +
    (∑ i, ∑ j,
      (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - h) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2 * w x) =
    η x *
      ((∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) +
       ∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) *
      Real.exp (-u x)
  simp only [← Finset.sum_mul, Matrix.sub_apply]
  dsimp only [w]
  ring
