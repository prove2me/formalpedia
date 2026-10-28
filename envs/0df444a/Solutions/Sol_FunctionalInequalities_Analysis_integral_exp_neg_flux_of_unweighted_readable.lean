-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_exp_neg_flux_of_unweighted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:36.822261+00:00
-- url     : https://prove2.me/submissions/4dde5bdd-9c32-4a2f-8607-f4a7b5471aa1

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

noncomputable section
section WeightedWeakHessianEvolution
open Matrix MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff
open scoped BigOperators
/-- Closed C1 multiplication by exp(-u) in a compact-test divergence identity. -/
 theorem solution {n : ℕ}
    {u c : EuclideanSpace ℝ (Fin n) → ℝ}
    {J : EuclideanSpace ℝ (Fin n) → Fin n → ℝ}
    (hu : ContDiff ℝ 1 u)
    (hJ : ∀ a : Fin n, LocallyIntegrable (fun x => J x a)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hc : LocallyIntegrable c (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hId : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ x, ∑ a : Fin n, J x a *
        fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ a)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, c x * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    LocallyIntegrable
      (fun x => Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x a *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let weight := fun x => Real.exp (-u x)
  have hweight : ContDiff ℝ 1 weight := hu.neg.exp
  have hdu (a : Fin n) : Continuous (fun x => fderiv ℝ u x (e a)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  let d := fun x => ∑ a : Fin n, J x a * fderiv ℝ u x (e a)
  have hd : LocallyIntegrable d (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_finsetSum Finset.univ (fun a _ => (hJ a).mul_continuous (hdu a))
  refine ⟨?_, ?_⟩
  · change LocallyIntegrable (fun x => weight x * (c x - d x)) volume
    simpa only [Pi.sub_apply] using
      LocallyIntegrable.continuous_mul hweight.continuous (hc.sub hd)
  · intro ψ hψ hψc
    let A := fun x => weight x * (∑ a : Fin n, J x a * fderiv ℝ ψ x (e a))
    let B := fun x => weight x * ψ x * d x
    let E := fun x => c x * (weight x * ψ x)
    have hdψ (a : Fin n) : Continuous (fun x => fderiv ℝ ψ x (e a)) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdψc (a : Fin n) : HasCompactSupport (fun x => fderiv ℝ ψ x (e a)) :=
      hψc.fderiv_apply ℝ (e a)
    have hAi (a : Fin n) : Integrable (fun x => weight x * (J x a * fderiv ℝ ψ x (e a)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      have hi := (hJ a).integrable_smul_left_of_hasCompactSupport
        (hweight.continuous.mul (hdψ a)) ((hdψc a).mul_left)
      convert hi using 1
      funext x
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    have hA : Integrable A (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [A, Finset.mul_sum] using
        integrable_finsetSum Finset.univ (fun a _ => hAi a)
    have hB : Integrable B (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [B, smul_eq_mul, Pi.mul_apply] using
        hd.integrable_smul_left_of_hasCompactSupport
          (hweight.continuous.mul hψ.continuous) hψc.mul_left
    have hE : Integrable E (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      have hi := hc.integrable_smul_left_of_hasCompactSupport
        (hweight.continuous.mul hψ.continuous) hψc.mul_left
      simpa only [E, smul_eq_mul, Pi.mul_apply, mul_comm] using hi
    have hderiv (x : EuclideanSpace ℝ (Fin n)) (a : Fin n) :
        fderiv ℝ (fun y => weight y * ψ y) x (e a) =
          weight x * fderiv ℝ ψ x (e a) - weight x * ψ x * fderiv ℝ u x (e a) := by
      have hux := (hu.differentiable one_ne_zero).differentiableAt (x := x)
      have hψx := (hψ.differentiable one_ne_zero).differentiableAt (x := x)
      have he := ((hux.hasFDerivAt.neg.exp).mul hψx.hasFDerivAt).fderiv
      change fderiv ℝ (fun y => Real.exp (-u y) * ψ y) x (e a) = _
      change fderiv ℝ (fun y => Real.exp (-u y) * ψ y) x = _ at he
      rw [he]
      simp only [_root_.add_apply, _root_.smul_apply,
        _root_.neg_apply, smul_eq_mul, Pi.neg_apply]
      dsimp [weight]
      ring
    have hleft (x : EuclideanSpace ℝ (Fin n)) :
        (∑ a : Fin n, J x a * fderiv ℝ (fun y => weight y * ψ y) x (e a)) =
          A x - B x := by
      simp only [hderiv]
      calc
        _ = ∑ a : Fin n, (weight x * (J x a * fderiv ℝ ψ x (e a)) -
            (weight x * ψ x) * (J x a * fderiv ℝ u x (e a))) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hid := hId (fun y => weight y * ψ y) (hweight.mul hψ) hψc.mul_left
    have hleftfun :
        (fun x => ∑ a : Fin n, J x a * fderiv ℝ (fun y => weight y * ψ y) x (e a)) =
          (fun x => A x - B x) := funext hleft
    have hab : (∫ x, A x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
        (∫ x, B x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, E x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      change (∫ x, ∑ a : Fin n, J x a *
        fderiv ℝ (fun y => weight y * ψ y) x (e a)) = -(∫ x, E x) at hid
      rw [hleftfun, integral_sub hA hB] at hid
      exact hid
    have hrhs : (fun x => weight x * (c x - d x) * ψ x) =
        (fun x => E x - B x) := by
      funext x
      dsimp [E, B]
      ring
    change (∫ x, A x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, weight x * (c x - d x) * ψ x)
    rw [hrhs, integral_sub hE hB]
    linarith only [hab]
