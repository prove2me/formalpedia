-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.map_density_shift_scale_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:53.633795+00:00
-- url     : https://prove2.me/submissions/f6338675-adda-4788-b68b-05125f34428a

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Density

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
end MeasurableSpace
end TiltTransport
end
end
end

open MeasureTheory FunctionalInequalities.Probability.Line
/-- **Push-forward under the fibrewise shear** `(a, η) ↦ (a, (F a + η)/σ)`: a density `w` on
`μ ⊗ ds` becomes `|σ| · w(a, σ s - F a)`, the inverse Jacobian of the shear. -/
 theorem solution {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [SFinite μ] (F : A → ℝ) (hF : Measurable F) (σ : ℝ) (hσ : σ ≠ 0)
    (w : A × ℝ → ENNReal) (hw : Measurable w) :
    ((μ.prod volume).withDensity w).map (fun p => (p.1, (F p.1 + p.2) / σ)) =
      (μ.prod volume).withDensity
        (fun p => ENNReal.ofReal |σ| * w (p.1, σ * p.2 - F p.1)) := by
  let e : A × ℝ ≃ᵐ A × ℝ :=
    { toFun p := (p.1, (F p.1 + p.2) / σ)
      invFun p := (p.1, σ * p.2 - F p.1)
      left_inv p := by
        apply Prod.ext
        · rfl
        · dsimp
          field_simp
          ring
      right_inv p := by
        apply Prod.ext
        · rfl
        · dsimp
          field_simp
          ring
      measurable_toFun := measurable_fst.prodMk
        (((hF.comp measurable_fst).add measurable_snd).div_const σ)
      measurable_invFun := measurable_fst.prodMk
        ((measurable_const.mul measurable_snd).sub (hF.comp measurable_fst)) }
  have hshift : MeasurePreserving (fun p : A × ℝ => (p.1, F p.1 + p.2))
      (μ.prod volume) (μ.prod volume) :=
    (MeasurePreserving.id μ).skew_product
      ((hF.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun x => map_add_left_eq_self volume (F x))
  have hreal : (volume : Measure ℝ).map (fun x => x / σ) =
      ENNReal.ofReal |σ| • volume := by
    simpa only [inv_inv, mul_comm, div_eq_mul_inv] using
      (Real.map_volume_mul_left (inv_ne_zero hσ))
  have hscale : (μ.prod volume).map (fun p : A × ℝ => (p.1, p.2 / σ)) =
      ENNReal.ofReal |σ| • μ.prod volume := by
    change (μ.prod volume).map (Prod.map id (fun x => x / σ)) = _
    rw [← Measure.map_prod_map μ volume measurable_id
      (show Measurable (fun x : ℝ => x / σ) from measurable_id.div_const σ),
      Measure.map_id, hreal, Measure.prod_smul_right]
  have hbase : (μ.prod volume).map e = ENNReal.ofReal |σ| • μ.prod volume := by
    change (μ.prod volume).map
      ((fun p : A × ℝ => (p.1, p.2 / σ)) ∘ (fun p : A × ℝ => (p.1, F p.1 + p.2))) = _
    rw [← Measure.map_map
      (measurable_fst.prodMk (measurable_snd.div_const σ)) hshift.measurable,
      hshift.map_eq, hscale]
  change ((μ.prod volume).withDensity w).map e = _
  rw [FunctionalInequalities.Probability.map_withDensity_measurableEquiv e (μ.prod volume) w hw, hbase, withDensity_smul_measure,
    ← withDensity_smul (ENNReal.ofReal |σ|)
      (show Measurable (fun y => w (e.symm y)) from hw.comp e.symm.measurable)]
  rfl
