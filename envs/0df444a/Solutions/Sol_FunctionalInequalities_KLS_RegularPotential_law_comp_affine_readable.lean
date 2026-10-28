-- Prove2me | solution 1 for FunctionalInequalities.KLS.RegularPotential.law_comp_affine_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:36:51.668529+00:00
-- url     : https://prove2.me/submissions/21aedae9-5e9b-4897-8d6f-8ad722c97167

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Affine
import Theorems.Thm_FunctionalInequalities_Probability_tilted_smul_pos_readable

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
universe u v
section TiltTransport
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]
/-- Pushing a density through a measurable equivalence: the new density is the old one composed with
the inverse. -/
theorem FunctionalInequalities.Probability.map_withDensity_measurableEquiv
    (e : A ≃ᵐ B) (μ : Measure A) (w : A → ENNReal) (hw : Measurable w) :
    (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ e.measurable,
    lintegral_withDensity_eq_lintegral_mul μ hw (show Measurable (fun x => φ (e x)) from hφ.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul (μ.map e) (show Measurable (fun y => w (e.symm y)) from hw.comp e.symm.measurable) hφ]
  simp only [Pi.mul_apply]
  rw [lintegral_map (show Measurable (fun y => w (e.symm y) * φ y) from (hw.comp e.symm.measurable).mul hφ) e.measurable]
  simp only [e.symm_apply_apply]
/-- The tilted measure transported through a measurable equivalence is the tilt of the image measure by
the composed weight. -/
theorem FunctionalInequalities.Probability.map_tilted_measurableEquiv
    (e : A ≃ᵐ B) (μ : Measure A) (f : A → ℝ) (hf : Measurable f) :
    (μ.tilted f).map e = (μ.map e).tilted (fun y => f (e.symm y)) := by
  have hZ : (∫ y, Real.exp (f (e.symm y)) ∂(μ.map e)) = ∫ x, Real.exp (f x) ∂μ := by
    simpa only [Function.comp_def, e.symm_apply_apply] using
      integral_map e.measurable.aemeasurable
        ((hf.comp e.symm.measurable).exp.aestronglyMeasurable)
  unfold Measure.tilted
  rw [Probability.map_withDensity_measurableEquiv e μ _ (hf.exp.div_const _).ennreal_ofReal, hZ]
end MeasurableSpace
end TiltTransport
end
end
end

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section InverseAffineEvaluation
omit [CompleteSpace E] [FiniteDimensional ℝ E]
theorem FunctionalInequalities.KLS.inverseAffineEquiv_apply (L : E ≃L[ℝ] E) (c y : E) :
    inverseAffineEquiv L c y = L.symm (y - c) := by
  change L.symm (y + -c) = L.symm (y - c)
  rw [sub_eq_add_neg]
theorem FunctionalInequalities.KLS.inverseAffineEquiv_symm_apply (L : E ≃L[ℝ] E) (c x : E) :
    (inverseAffineEquiv L c).symm x = L x + c := rfl
end InverseAffineEvaluation
omit [CompleteSpace E] in
/-- Lebesgue measure under the inverse affine map scales by `|det L⁻¹|⁻¹`. -/
theorem FunctionalInequalities.KLS.inverseAffine_map_volume (L : E ≃L[ℝ] E) (c : E) :
    (volume : Measure E).map (inverseAffineEquiv L c) =
      ENNReal.ofReal |(LinearMap.det (L.symm : E →ₗ[ℝ] E))⁻¹| • volume := by
  have hdet : LinearMap.det (L.symm : E →ₗ[ℝ] E) ≠ 0 := L.symm.toLinearEquiv.isUnit_det'.ne_zero
  have ht : (volume : Measure E).map (fun y => y - c) = volume := by
    simp_rw [sub_eq_add_neg]
    exact Measure.IsAddRightInvariant.map_add_right_eq_self (-c)
  have heq : (inverseAffineEquiv L c : E → E) =
      (fun y => L.symm y) ∘ (fun y => y - c) := by
    funext y
    exact inverseAffineEquiv_apply L c y
  rw [heq, ← Measure.map_map L.symm.continuous.measurable (by fun_prop), ht]
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
section RegularAffineLaws
variable {V : E → ℝ} {a b : ℝ} (hV : FunctionalInequalities.KLS.RegularPotential V a b)
include hV in
/-- **The law of `V ∘ (L · + c)` is the image of the law of `V` under `y ↦ L⁻¹(y − c)`** (the Jacobian
constant cancels in the normalization). -/
theorem solution
    (L : E ≃L[ℝ] E) (c : E) :
    ((FunctionalInequalities.KLS.RegularPotential.comp_affine hV L c).law : Measure E) =
      (hV.law : Measure E).map (fun y => L.symm (y - c)) := by
  let e := FunctionalInequalities.KLS.inverseAffineEquiv L c
  have ht := FunctionalInequalities.Probability.map_tilted_measurableEquiv e (volume : Measure E) (-V) hV.temperate.1.continuous.neg.measurable
  have hmap := FunctionalInequalities.KLS.inverseAffine_map_volume L c
  have hdet : LinearMap.det (L.symm : E →ₗ[ℝ] E) ≠ 0 := L.symm.toLinearEquiv.isUnit_det'.ne_zero
  have hJ : 0 < |(LinearMap.det (L.symm : E →ₗ[ℝ] E))⁻¹| := abs_pos.2 (inv_ne_zero hdet)
  rw [hmap, FunctionalInequalities.Probability.tilted_smul_pos_readable _ _ hJ] at ht
  have hf : (fun y => (-V) (e.symm y)) = -fun x => V (L x + c) := by
    funext y
    rw [show e.symm y = L y + c from FunctionalInequalities.KLS.inverseAffineEquiv_symm_apply L c y]
    rfl
  rw [hf] at ht
  have heq : (e : E → E) = fun y => L.symm (y - c) := funext (FunctionalInequalities.KLS.inverseAffineEquiv_apply L c)
  rw [heq] at ht
  exact ht.symm
