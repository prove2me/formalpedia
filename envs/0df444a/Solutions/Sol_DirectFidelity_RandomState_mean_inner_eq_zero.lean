-- Prove2me | solution 1 for DirectFidelity.RandomState.mean_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:53:18.462214+00:00
-- url     : https://prove2.me/submissions/c7a67ab1-31f4-4d69-972f-7ee7f75712eb

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting
namespace DirectFidelity.RandomState

open MeasureTheory

open scoped Pointwise in
theorem _root_.solution (n : ℕ) (φ : E n) :
    Integrable (fun ψ : Metric.sphere (0 : E n) 1 => inner ℂ φ (ψ : E n)) (unifSphere n) ∧
      ∫ ψ, inner ℂ φ (ψ : E n) ∂(unifSphere n) = 0 := by
  have hneg : MeasurePreserving (fun ψ : Metric.sphere (0 : E n) 1 => -ψ) (unifSphere n) (unifSphere n) := by
    have hc : Continuous (fun ψ : Metric.sphere (0 : E n) 1 => -ψ) := continuous_neg
    refine ⟨hc.measurable, ?_⟩
    unfold unifSphere
    rw [Measure.map_smul]
    congr 1
    ext s hs
    rw [Measure.map_apply hc.measurable hs,
      Measure.toSphere_apply' _ (hc.measurable hs), Measure.toSphere_apply' _ hs]
    congr 1
    have : (Set.Ioo (0:ℝ) 1 • (Subtype.val '' ((fun ψ : Metric.sphere (0 : E n) 1 => -ψ) ⁻¹' s)))
        = -(Set.Ioo (0:ℝ) 1 • (Subtype.val '' s)) := by
      rw [← Set.smul_neg]
      congr 1
      ext v
      simp only [Set.mem_neg, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨-a, ha, by simp⟩
      · rintro ⟨a, ha, h⟩
        refine ⟨-a, by simpa using ha, ?_⟩
        rw [coe_neg_sphere, h, neg_neg]
    rw [this, Measure.measure_neg]
  have hint : Integrable (fun ψ : Metric.sphere (0 : E n) 1 => inner ℂ φ (ψ : E n)) (unifSphere n) := by
    have hfin : IsFiniteMeasure (unifSphere n) := by
      unfold unifSphere
      refine ⟨?_⟩
      rw [Measure.smul_apply, smul_eq_mul]
      exact lt_of_le_of_lt (ENNReal.inv_mul_le_one _) ENNReal.one_lt_top
    have hc : Continuous (fun ψ : Metric.sphere (0 : E n) 1 => inner ℂ φ (ψ : E n)) :=
      continuous_const.inner continuous_subtype_val
    refine Integrable.of_bound hc.aestronglyMeasurable ‖φ‖ (Filter.Eventually.of_forall fun ψ => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_eq_of_mem_sphere ψ, mul_one]
  refine ⟨hint, ?_⟩
  have hemb : MeasurableEmbedding (fun ψ : Metric.sphere (0 : E n) 1 => -ψ) :=
    (Homeomorph.neg (Metric.sphere (0 : E n) 1)).measurableEmbedding
  have h := hneg.integral_comp hemb (fun ψ : Metric.sphere (0 : E n) 1 => inner ℂ φ (ψ : E n))
  simp only [coe_neg_sphere, inner_neg_right, integral_neg] at h
  exact CharZero.neg_eq_self_iff.1 h

end DirectFidelity.RandomState

