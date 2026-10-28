-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.source_stein_identity_of_bounded_lipschitz_test_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:01.417431+00:00
-- url     : https://prove2.me/submissions/f1bcc1e7-b186-4d8b-967b-0a901c15276b

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HessianStein
import Theorems.Thm_FunctionalInequalities_Analysis_integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_readable
import Theorems.Thm_FunctionalInequalities_Probability_Stein_chain_coordinate_of_differentiableAt_gradient_readable

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section WeakSourceSteinIdentity
open MeasureTheory Filter
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace
set_option maxHeartbeats 600000 in
/-- Weak source Stein identity at a C1 potential with Lipschitz gradient and mass-one exponential weight: for every C1 bounded
globally Lipschitz test `f` the coordinate pairing `∫ ∂ᵢu · f(∇u)` equals `∫ ∑ⱼ (∇²u)ᵢⱼ ∂ⱼf(∇u)` (both integrable);
no C2, global inverse or kernel premise. -/
theorem solution {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lf : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hf : ContDiff ℝ 1 f) (hfLip : LipschitzWith Lf f)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) (i : Fin n) :
    Integrable (fun y => gradient u y i * f (gradient u y))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    Integrable (fun y => ∑ j, FunctionalInequalities.Probability.Stein.hessianMatrix u y i j * gradient f (gradient u y) j)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    (∫ y, gradient u y i * f (gradient u y)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ y, (∑ j, FunctionalInequalities.Probability.Stein.hessianMatrix u y i j * gradient f (gradient u y) j)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  let eta := f ∘ gradient u
  let mu : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted (-u)
  have hpair := FunctionalInequalities.Analysis.integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_readable
    hL (hfLip.comp hG) C (fun y => hbound (gradient u y)) hnorm
    (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hleft : (fun y => eta y * fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i)) =ᵐ[mu]
      (fun y => gradient u y i * f (gradient u y)) := by
    filter_upwards [] with y
    have hdu : fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i) = gradient u y i := by
      rw [← inner_gradient_left, EuclideanSpace.inner_basisFun_real]
    dsimp only [eta, Function.comp_apply]
    rw [hdu, mul_comm]
  have hchain : (fun y => fderiv ℝ eta y (EuclideanSpace.basisFun (Fin n) ℝ i)) =ᵐ[mu]
      (fun y => ∑ j, FunctionalInequalities.Probability.Stein.hessianMatrix u y i j * gradient f (gradient u y) j) := by
    have hac : mu ≪ (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      tilted_absolutelyContinuous _ _
    filter_upwards [hac.ae_le (hG.ae_differentiableAt (μ := volume))] with y hy
    exact FunctionalInequalities.Probability.Stein.chain_coordinate_of_differentiableAt_gradient_readable hu hf hy i
  refine ⟨hpair.2.1.congr hleft, hpair.1.congr hchain, ?_⟩
  calc
    _ = ∫ y, eta y * fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i) ∂mu :=
      (integral_congr_ae hleft).symm
    _ = ∫ y, fderiv ℝ eta y (EuclideanSpace.basisFun (Fin n) ℝ i) ∂mu := hpair.2.2.symm
    _ = _ := integral_congr_ae hchain
