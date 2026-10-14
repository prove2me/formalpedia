-- Prove2me | solution 1 for DbarRegularity.lintegral_fun_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T19:28:51.158742+00:00
-- url     : https://prove2.me/submissions/f5dc6879-44d7-4dcb-b11c-64f95f3f407a

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- Lower Lebesgue integral of a radial function on `ℝ^d`, `d ≥ 1`:
`∫ F(|x|) dx = d |B(0,1)| ∫₀^∞ r^{d-1} F(r) dr` for measurable `F : ℝ → [0, ∞]`. -/
theorem lintegral_fun_norm_eq {d : ℕ} (hd : 0 < d) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x : EuclideanSpace ℝ (Fin d), F ‖x‖ =
      d * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * F r := by
  have : NeZero d := ⟨hd.ne'⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  calc ∫⁻ x : EuclideanSpace ℝ (Fin d), F ‖x‖
      = ∫⁻ x : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set (EuclideanSpace ℝ (Fin d))), F ‖x.1‖
          ∂(volume.comap Subtype.val) := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl fun x => F ‖x‖,
          restrict_compl_singleton]
    _ = ∫⁻ z, F z.2 ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1))) := by
        have := (Measure.measurePreserving_homeomorphUnitSphereProd
          (volume : Measure (EuclideanSpace ℝ (Fin d)))).lintegral_comp_emb
          (Homeomorph.measurableEmbedding _) (fun z => F z.2)
        simpa using this
    _ = (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere univ *
          ∫⁻ r, F r ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1)) := by
        rw [lintegral_prod (fun z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Ioi (0 : ℝ) => F z.2)
          ((hF.comp measurable_subtype_coe).comp measurable_snd).aemeasurable]
        simp [mul_comm]
    _ = _ := by
        rw [Measure.toSphere_apply_univ, hfin, Measure.volumeIoiPow,
          lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
            (g := fun r : Ioi (0 : ℝ) => F r) (hF.comp measurable_subtype_coe)]
        exact congrArg _ (lintegral_subtype_comap measurableSet_Ioi
          (fun r => ENNReal.ofReal (r ^ (d - 1)) * F r))

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

theorem solution {d : ℕ} (hd : 0 < d) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x : EuclideanSpace ℝ (Fin d), F ‖x‖ =
      d * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * F r :=
  lintegral_fun_norm_eq hd F hF
