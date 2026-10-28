-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.source_affine_stein_identity_of_bounded_lipschitz_test_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:46.81596+00:00
-- url     : https://prove2.me/submissions/c66723a2-a937-49dc-bb64-83901bd6957e

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HessianStein
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_source_stein_identity_of_bounded_lipschitz_test_readable

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
noncomputable section
open scoped RealInnerProductSpace
section
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_comp_affine {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (S : E →L[ℝ] F) (z : F) {f : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (S x + z)) :
    gradient (fun y => f (S y + z)) x = S.adjoint (gradient f (S x + z)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left]
  exact congrArg (fun T : E →L[ℝ] ℝ => T v)
    (hf.hasFDerivAt.comp x (S.hasFDerivAt.add_const z)).fderiv
end
end
end
end

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
section
set_option maxHeartbeats 600000 in
theorem FunctionalInequalities.KLS.LogConcave.source_directional_stein_identity_of_bounded_lipschitz_test {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lf : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hf : ContDiff ℝ 1 f) (hfLip : LipschitzWith Lf f)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => ⟪gradient u y, v⟫ * f (gradient u y))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    Integrable (fun y => ⟪v, action (hessianMatrix u y) (gradient f (gradient u y))⟫)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    (∫ y, ⟪gradient u y, v⟫ * f (gradient u y)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ y, ⟪v, action (hessianMatrix u y) (gradient f (gradient u y))⟫
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  classical
  let mu : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted (-u)
  let A (i : Fin n) (y : EuclideanSpace ℝ (Fin n)) := gradient u y i * f (gradient u y)
  let B (i : Fin n) (y : EuclideanSpace ℝ (Fin n)) :=
    ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j
  have hp (i : Fin n) := source_stein_identity_of_bounded_lipschitz_test_readable hu hL hG hnorm hf hfLip C hbound i
  have hA : Integrable (fun y => ∑ i, v i * A i y) mu :=
    integrable_finsetSum Finset.univ fun i _ => (hp i).1.const_mul (v i)
  have hB : Integrable (fun y => ∑ i, v i * B i y) mu :=
    integrable_finsetSum Finset.univ fun i _ => (hp i).2.1.const_mul (v i)
  have heqA (y : EuclideanSpace ℝ (Fin n)) : (∑ i, v i * A i y) =
      ⟪gradient u y, v⟫ * f (gradient u y) := by
    simp only [PiLp.inner_apply, Real.inner_apply, Finset.sum_mul, A]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have heqB (y : EuclideanSpace ℝ (Fin n)) : (∑ i, v i * B i y) =
      ⟪v, action (hessianMatrix u y) (gradient f (gradient u y))⟫ := by
    simp only [PiLp.inner_apply, Real.inner_apply, action, Matrix.mulVec, dotProduct, B]
  refine ⟨hA.congr (ae_of_all _ heqA), hB.congr (ae_of_all _ heqB), ?_⟩
  calc
    _ = ∫ y, ∑ i, v i * A i y ∂mu := (integral_congr_ae (ae_of_all _ heqA)).symm
    _ = ∑ i, v i * ∫ y, A i y ∂mu := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hp i).1.const_mul (v i))]
      simp only [integral_const_mul, A, mu]
    _ = ∑ i, v i * ∫ y, B i y ∂mu := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(hp i).2.2]
    _ = ∫ y, ∑ i, v i * B i y ∂mu := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hp i).2.1.const_mul (v i))]
      simp only [integral_const_mul, B, mu]
    _ = _ := integral_congr_ae (ae_of_all _ heqB)
end
end
noncomputable section
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
set_option maxHeartbeats 600000 in
theorem solution {n : ℕ}
    {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
    (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (z v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    Integrable (fun y => ⟪S.adjoint v,
      FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    (∫ y, ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ y, ⟪S.adjoint v,
        FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  have hf : ContDiff ℝ 1 (fun x => h (S x + z)) := hh.comp (S.contDiff.add contDiff_const)
  have hp := FunctionalInequalities.KLS.LogConcave.source_directional_stein_identity_of_bounded_lipschitz_test hu hL hG hnorm
    hf (hhLip.comp (S.lipschitz.add (LipschitzWith.const z))) C (fun x => hbound (S x + z)) (S.adjoint v)
  have hleft (y : EuclideanSpace ℝ (Fin n)) :
      ⟪gradient u y, S.adjoint v⟫ * h (S (gradient u y) + z) =
      ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z) := by
    rw [S.adjoint_inner_right]
  have hright (y : EuclideanSpace ℝ (Fin n)) :
      ⟪S.adjoint v, FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u y) (gradient (fun x => h (S x + z)) (gradient u y))⟫ =
      ⟪S.adjoint v, FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫ := by
    rw [FunctionalInequalities.Analysis.BakryEmery.gradient_comp_affine S z (hh.differentiable one_ne_zero _)]
  refine ⟨hp.1.congr (ae_of_all _ hleft), hp.2.1.congr (ae_of_all _ hright), ?_⟩
  exact (integral_congr_ae (ae_of_all _ hleft)).symm.trans (hp.2.2.trans
    (integral_congr_ae (ae_of_all _ hright)))
