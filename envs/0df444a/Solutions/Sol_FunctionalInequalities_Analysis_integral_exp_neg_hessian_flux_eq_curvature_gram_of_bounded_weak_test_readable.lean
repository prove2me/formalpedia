-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:31.386984+00:00
-- url     : https://prove2.me/submissions/15d1bfb2-2dcf-4a57-bd8b-fb2c9f0ae479

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution
import Theorems.Thm_FunctionalInequalities_Analysis_integral_exp_neg_hessian_flux_eq_curvature_gram_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_flux_eq_neg_forcing_of_bounded_weak_test_readable

noncomputable section
section BoundedWeightedHessianTesting
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology
private theorem FunctionalInequalities.Analysis.compact_local_memLp_two_continuous_mul {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hχ : Continuous χ) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => χ x * f x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  intro S hS
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hχ.continuousOn
  have htop : MemLp χ (⊤ : ENNReal)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    memLp_top_of_bound hχ.measurable.aestronglyMeasurable.restrict C
      (ae_restrict_of_forall_mem hS.measurableSet hC)
  exact (hf S hS).mul' htop
/-- The weighted weak Hessian evolution identity extended to a bounded compactly supported test `η` whose
coordinate weak derivatives are compactly supported and globally L2, with both sides integrable. -/
theorem solution {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j)
          (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst : ∀ i : Fin n,
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
          -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
          ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ b : Fin n, FunctionalInequalities.Analysis.HasWeakDerivAlong η (a b) (EuclideanSpace.basisFun (Fin n) ℝ b))
    (hac : ∀ b : Fin n, HasCompactSupport (a b))
    (ha2 : ∀ b : Fin n, MemLp (a b) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ b : Fin n, Integrable
        (fun x => Real.exp (-u x) * J x i j b * a b x)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * η x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * a b x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * η x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
  let J := fun x i j b => ∑ c : Fin n, R x c b * T x c i j
  let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
    (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
    (R x * (Matrix.of fun b c => T x i b c) * R x *
      (Matrix.of fun b c => T x j b c)).trace
  let wgt := fun x => Real.exp (-u x)
  have hdata := FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_readable
    hu hL hG hW hF hdet T hT hInv hFirst
  change ∀ i j : Fin n, _
  intro i j
  have hwgt : Continuous wgt := Real.continuous_exp.comp hu.continuous.neg
  have hJw (b : Fin n) : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => wgt x * J x i j b) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    FunctionalInequalities.Analysis.compact_local_memLp_two_continuous_mul ((hdata i j).1 b) hwgt
  have hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, ∑ b : Fin n, (wgt x * J x i j b) *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, (wgt x * E x i j) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    intro ψ hψ hψc
    calc
      _ = ∫ x, wgt x * (∑ b : Fin n, J x i j b *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          simp only [wgt, J, R, Finset.mul_sum, Finset.sum_mul, mul_assoc])
      _ = _ := (hdata i j).2.2.2 ψ hψ hψc
  have ht := FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test_readable
    hJw (hdata i j).2.2.1 hId hη hbound hηc hweak hac ha2
  refine ⟨ht.1, ht.2.1, ?_⟩
  calc
    _ = ∫ x, ∑ b : Fin n, (wgt x * J x i j b) * a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [wgt, J, R, Finset.mul_sum, Finset.sum_mul, mul_assoc])
    _ = _ := ht.2.2
