-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integrable_weak_generator_densities_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:04.218625+00:00
-- url     : https://prove2.me/submissions/0eab6c0c-b0e3-4ecf-9f22-a129f692abf0

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_inv_hessianMatrix_mul_of_bounded_compact_readable
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable

section
noncomputable section
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
/-- Continuity of the Hessian entries. -/
theorem FunctionalInequalities.Probability.Stein.hessian_entry_continuous {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ) (i j : Fin n) :
    Continuous (fun y => hessianMatrix φ y i j) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  exact ((h1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
end
end
end

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
section GeneratorIntegrability
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
private lemma FunctionalInequalities.Analysis.weak_generator_compact_hessian_entry {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hηc : HasCompactSupport η) (i j : Fin n) :
    HasCompactSupport (fun x => hessianMatrix η x i j) := by
  change HasCompactSupport
    ((fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      A (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) ∘
      fderiv ℝ (fderiv ℝ η))
  exact ((hηc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).comp_left (by simp)
private lemma FunctionalInequalities.Analysis.weak_generator_compact_apply {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hgc : HasCompactSupport g) :
    HasCompactSupport (fun x => A x (g x)) := by
  apply hgc.mono'
  intro x hx
  by_contra hn
  have hz : g x = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hx
  change A x (g x) = 0
  rw [hz, map_zero]
/-- Genuine integrability for the weak inverse-Hessian generator, its exchanged
test density and the absolute RHS of the Hessian-increment energy estimate. -/
theorem solution {n : ℕ}
    {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : Continuous (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : Continuous w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    Integrable (fun x => η x *
      (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => w x *
      (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x =>
      |η x + (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have he : Continuous (fun x => Real.exp (-u x)) :=
    Real.continuous_exp.comp hu.neg
  have hDV : Continuous (fun x => fderiv ℝ V (gradient u x)) :=
    (hV.continuous_fderiv one_ne_zero).comp hG.continuous
  have hgradη : Continuous (gradient η) :=
    FunctionalInequalities.Analysis.BakryEmery.continuous_gradient (hη.of_le (by norm_num))

  have htrace :
      ∀ {f a : EuclideanSpace ℝ (Fin n) → ℝ},
        (∀ i j, Integrable
          (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
            (a x * FunctionalInequalities.Probability.Stein.hessianMatrix f x j i))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
        Integrable
          (fun x => a x * ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix f x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro f a hi
    have hs := integrable_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
    apply hs.congr
    filter_upwards [] with x
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

  have hηe : Continuous (fun x => η x * Real.exp (-u x)) :=
    hη.continuous.mul he
  have hηec : HasCompactSupport (fun x => η x * Real.exp (-u x)) :=
    hηc.mul_right
  obtain ⟨B, hB⟩ := hηec.exists_bound_of_continuous hηe
  have hwt : Integrable
      (fun x => (η x * Real.exp (-u x)) *
        ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix w x).trace)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply htrace
    intro i j
    apply FunctionalInequalities.Analysis.integrable_inv_hessianMatrix_mul_of_bounded_compact_readable hG hF hdet
      (hηe.measurable.mul (FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry w j i))
      hηec.mul_right (C := B * (Gw : ℝ)) ?_ i j
    intro x
    change ‖(η x * Real.exp (-u x)) * FunctionalInequalities.Probability.Stein.hessianMatrix w x j i‖ ≤ B * (Gw : ℝ)
    rw [norm_mul]
    exact mul_le_mul (hB x)
      (FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable hGw x j i)
      (norm_nonneg _) (le_trans (norm_nonneg _) (hB x))
  have hwd : Integrable
      (fun x => η x * fderiv ℝ V (gradient u x) (gradient w x) *
        Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ((hη.continuous.mul (hDV.clm_apply hGw.continuous)).mul he).integrable_of_hasCompactSupport
      (hηc.mul_right.mul_right)
  have hfirst : Integrable
      (fun x => η x *
        (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix w x).trace -
          fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply (hwt.sub hwd).congr
    filter_upwards [] with x
    change
      (η x * Real.exp (-u x)) *
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix w x).trace -
        η x * fderiv ℝ V (gradient u x) (gradient w x) * Real.exp (-u x) =
      η x * (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
    ring

  have hηdc : HasCompactSupport
      (fun x => fderiv ℝ V (gradient u x) (gradient η x)) :=
    FunctionalInequalities.Analysis.weak_generator_compact_apply (fun x => fderiv ℝ V (gradient u x))
      (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hηc)
  have hprimed :
      ∀ {a : EuclideanSpace ℝ (Fin n) → ℝ}, Continuous a →
        Integrable
          (fun x => a x *
            (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
              fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a ha
    have hat : Integrable
        (fun x => (a x * Real.exp (-u x)) *
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply htrace
      intro i j
      have hc : Continuous
          (fun x => (a x * Real.exp (-u x)) * FunctionalInequalities.Probability.Stein.hessianMatrix η x j i) :=
        (ha.mul he).mul (FunctionalInequalities.Probability.Stein.hessian_entry_continuous hη j i)
      have hcc : HasCompactSupport
          (fun x => (a x * Real.exp (-u x)) * FunctionalInequalities.Probability.Stein.hessianMatrix η x j i) :=
        (FunctionalInequalities.Analysis.weak_generator_compact_hessian_entry hηc j i).mul_left
      obtain ⟨C, hC⟩ := hcc.exists_bound_of_continuous hc
      exact FunctionalInequalities.Analysis.integrable_inv_hessianMatrix_mul_of_bounded_compact_readable
        hG hF hdet hc.measurable hcc hC i j
    have had : Integrable
        (fun x => a x * fderiv ℝ V (gradient u x) (gradient η x) *
          Real.exp (-u x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      ((ha.mul (hDV.clm_apply hgradη)).mul he).integrable_of_hasCompactSupport
        (hηdc.mul_left.mul_right)
    apply (hat.sub had).congr
    filter_upwards [] with x
    change
      (a x * Real.exp (-u x)) *
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
        a x * fderiv ℝ V (gradient u x) (gradient η x) * Real.exp (-u x) =
      a x * (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
    ring

  refine ⟨hfirst, hprimed hw, ?_⟩
  have hLη : Integrable
      (fun x => (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [one_mul] using
      (hprimed (a := fun _ => (1 : ℝ)) continuous_const)
  have hsum : Integrable
      (fun x => (η x +
        (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
          fderiv ℝ V (gradient u x) (gradient η x))) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply ((hηe.integrable_of_hasCompactSupport hηec).add hLη).congr
    filter_upwards [] with x
    exact (add_mul _ _ _).symm
  simpa only [abs_mul, Real.abs_exp] using hsum.abs
