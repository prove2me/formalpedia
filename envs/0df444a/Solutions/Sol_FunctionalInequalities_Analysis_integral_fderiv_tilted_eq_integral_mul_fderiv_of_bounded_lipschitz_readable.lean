-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:03.524294+00:00
-- url     : https://prove2.me/submissions/888da402-b0de-42b6-a172-497f7bc2085a

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_LipschitzHessian
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_bounded_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_exp_neg_of_lipschitz_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_lipschitz_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_eq_zero_of_integrable_weak_derivative_readable

section
noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section SharedCompactLocalTools
open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace Topology
section
/-- A continuous function is essentially bounded on every compact set. -/
theorem FunctionalInequalities.Analysis.memLp_top_restrict_of_continuous {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.measurable.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC x hx
end
end SharedCompactLocalTools
end
end

noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped RealInnerProductSpace
section BoundedLipschitzTiltedIBP
open MeasureTheory Filter Set
open scoped ContDiff Topology
set_option maxHeartbeats 800000 in
/-- Weighted integration by parts for a bounded globally Lipschitz test `η` against the normalized exponential tilt of a
globally Lipschitz potential `U`: both pairings are integrable and `∫ D_v η dν = ∫ η D_v U dν`; all finite dimensions. -/
theorem solution {n : ℕ}
    {U eta : EuclideanSpace ℝ (Fin n) → ℝ} {L Leta : NNReal}
    (hU : LipschitzWith L U) (heta : LipschitzWith Leta eta)
    (C : ℝ) (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hnorm : (∫ x, Real.exp (-U x) ∂volume) = 1)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => fderiv ℝ eta x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    Integrable (fun x => eta x * fderiv ℝ U x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    (∫ x, fderiv ℝ eta x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) =
      ∫ x, eta x * fderiv ℝ U x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) := by
  let mu : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted (-U)
  have hexp : Integrable (fun x => Real.exp (-U x)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let : IsProbabilityMeasure mu := isProbabilityMeasure_tilted hexp
  have hdf (F : EuclideanSpace ℝ (Fin n) → ℝ) {K : NNReal} (hF : LipschitzWith K F) (x) :
      ‖fderiv ℝ F x v‖ ≤ (K : ℝ) * ‖v‖ :=
    ((fderiv ℝ F x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg v))
  have hdmeas (F : EuclideanSpace ℝ (Fin n) → ℝ) :
      Measurable (fun x => fderiv ℝ F x v) :=
    (continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ F)
  have hdet : Integrable (fun x => fderiv ℝ eta x v) mu :=
    (integrable_const ((Leta : ℝ) * ‖v‖)).mono' (hdmeas eta).aestronglyMeasurable
      (ae_of_all _ (hdf eta heta))
  have het : Integrable eta mu :=
    (integrable_const C).mono' heta.continuous.measurable.aestronglyMeasurable
      (ae_of_all _ hbound)
  have hedu : Integrable (fun x => eta x * fderiv ℝ U x v) mu := by
    apply (het.norm.const_mul ((L : ℝ) * ‖v‖)).mono'
      (heta.continuous.measurable.mul (hdmeas U)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖eta x * fderiv ℝ U x v‖ ≤ _
    rw [norm_mul]
    nlinarith [hdf U hU x, norm_nonneg (eta x)]
  obtain ⟨hwexp, hdexp⟩ := FunctionalInequalities.Analysis.hasWeakDerivAlong_exp_neg_of_lipschitz_readable hU v
  have hweta := FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_readable heta v
  have hetderiv (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => fderiv ℝ eta x v) 2 (volume.restrict S) := by
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    apply MemLp.of_bound (hdmeas eta).aestronglyMeasurable ((Leta : ℝ) * ‖v‖)
    exact ae_of_all _ (hdf eta heta)
  have hw := (hwexp.mul_of_locally_bounded_readable hweta
    (fun S hS => FunctionalInequalities.Analysis.memLp_top_restrict_of_continuous (Real.continuous_exp.comp hU.continuous.neg) S hS)
    (FunctionalInequalities.Analysis.memLp_top_restrict_of_continuous heta.continuous) hdexp hetderiv).1
  have hleft : Integrable (fun x => Real.exp (-U x) * eta x) volume := by
    simpa only [Pi.neg_apply, smul_eq_mul] using (integrable_tilted_iff hexp eta).mp het
  have hright1 : Integrable (fun x => Real.exp (-U x) * (eta x * fderiv ℝ U x v)) volume := by
    simpa only [Pi.neg_apply, smul_eq_mul] using
      (integrable_tilted_iff hexp (fun x => eta x * fderiv ℝ U x v)).mp hedu
  have hright2 : Integrable (fun x => Real.exp (-U x) * fderiv ℝ eta x v) volume := by
    simpa only [Pi.neg_apply, smul_eq_mul] using
      (integrable_tilted_iff hexp (fun x => fderiv ℝ eta x v)).mp hdet
  have hprod : Integrable (fun x => (-Real.exp (-U x) * fderiv ℝ U x v) * eta x +
      Real.exp (-U x) * fderiv ℝ eta x v) volume := by
    apply (hright1.neg.add hright2).congr
    filter_upwards [] with x
    change -(Real.exp (-U x) * (eta x * fderiv ℝ U x v)) +
      Real.exp (-U x) * fderiv ℝ eta x v = _
    ring
  have hz := FunctionalInequalities.Analysis.integral_eq_zero_of_integrable_weak_derivative_readable hw hleft hprod
  have heq : (∫ x, (-Real.exp (-U x) * fderiv ℝ U x v) * eta x +
      Real.exp (-U x) * fderiv ℝ eta x v ∂volume) =
      -(∫ x, Real.exp (-U x) * (eta x * fderiv ℝ U x v) ∂volume) +
        ∫ x, Real.exp (-U x) * fderiv ℝ eta x v ∂volume := by
    calc
      _ = ∫ x, -(Real.exp (-U x) * (eta x * fderiv ℝ U x v)) +
          Real.exp (-U x) * fderiv ℝ eta x v ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x, -(Real.exp (-U x) * (eta x * fderiv ℝ U x v)) ∂volume) +
          ∫ x, Real.exp (-U x) * fderiv ℝ eta x v ∂volume :=
        integral_add hright1.neg hright2
      _ = _ := by rw [integral_neg]
  have htilt (k : EuclideanSpace ℝ (Fin n) → ℝ) :
      (∫ x, k x ∂mu) = ∫ x, Real.exp (-U x) * k x ∂volume := by
    change (∫ x, k x ∂volume.tilted (-U)) = _
    rw [integral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul]
  refine ⟨hdet, hedu, ?_⟩
  change (∫ x, fderiv ℝ eta x v ∂mu) = ∫ x, eta x * fderiv ℝ U x v ∂mu
  rw [htilt, htilt]
  linarith
