-- Prove2me | solution 1 for BoundedNV.Pooling.eq63_standardized_cost
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:41:57.249825+00:00
-- url     : https://prove2.me/submissions/ecfb84b6-ba29-44af-b579-7de4c2978e31

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Canonical
set_option autoImplicit false
open MeasureTheory ProbabilityTheory BoundedNV.Pooling

theorem BNP_demand_map (μ σ : ℝ) (hσ : 0 < σ) :
    InventoryControl.newsboyDemand μ σ = (gaussianReal 0 1).map (fun t => μ + σ * t) := by
  have h1 : (gaussianReal 0 1).map (fun t => μ + σ * t) =
      ((gaussianReal 0 1).map (σ * ·)).map (μ + ·) := by
    rw [Measure.map_map (measurable_const_add μ) (measurable_const_mul σ)]
    rfl
  rw [h1, gaussianReal_map_const_mul, gaussianReal_map_const_add]
  unfold InventoryControl.newsboyDemand
  congr 1
  · simp
  · apply NNReal.eq
    simp [Real.coe_toNNReal _ (sq_nonneg σ)]

theorem BNP_integrable_min (z : ℝ) : Integrable (fun t : ℝ => min t z) (gaussianReal 0 1) := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  exact hid.inf (integrable_const z)

theorem BNP_int_id : ∫ t : ℝ, t ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal

theorem solution (h b μ σ z : ℝ)
    (hh : 0 < h) (hb : 0 < b) (hσ : 0 < σ) :
    InventoryControl.newsboyCost h b μ σ (μ + σ * z) =
      -(σ * canonProfit (h + b) h z) := by
  unfold InventoryControl.newsboyCost canonProfit
  have hmeas : Continuous (fun x => InventoryControl.newsboyLoss h b (μ + σ * z) x) := by
    unfold InventoryControl.newsboyLoss; fun_prop
  rw [BNP_demand_map μ σ hσ, integral_map (φ := fun t : ℝ => μ + σ * t) (by fun_prop : Measurable (fun t : ℝ => μ + σ * t)).aemeasurable hmeas.aestronglyMeasurable]
  · have hint := BNP_integrable_min z
    have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
      memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
    have e : ∀ t : ℝ, InventoryControl.newsboyLoss h b (μ + σ * z) (μ + σ * t) =
        σ * (h * (z - min t z) + b * (t - min t z)) := by
      intro t
      unfold InventoryControl.newsboyLoss
      rcases le_total t z with hl | hl
      · have a1 : 0 ≤ μ + σ * z - (μ + σ * t) := by nlinarith
        have a2 : μ + σ * t - (μ + σ * z) ≤ 0 := by nlinarith
        rw [max_eq_left a1, max_eq_right a2, min_eq_left hl]; ring
      · have a1 : μ + σ * z - (μ + σ * t) ≤ 0 := by nlinarith
        have a2 : 0 ≤ μ + σ * t - (μ + σ * z) := by nlinarith
        rw [max_eq_right a1, max_eq_left a2, min_eq_right hl]; ring
    simp only [Function.comp_def, e]
    rw [integral_const_mul]
    have i1 : Integrable (fun t : ℝ => h * (z - min t z)) (gaussianReal 0 1) :=
      ((integrable_const z).sub hint).const_mul h
    have i2 : Integrable (fun t : ℝ => b * (t - min t z)) (gaussianReal 0 1) :=
      (hid.sub hint).const_mul b
    have : ∫ t : ℝ, (h * (z - min t z) + b * (t - min t z)) ∂(gaussianReal 0 1) =
        h * z - h * (∫ t, min t z ∂(gaussianReal 0 1)) + (b * 0 - b * ∫ t, min t z ∂(gaussianReal 0 1)) := by
      rw [integral_add i1 i2, integral_const_mul, integral_const_mul,
        integral_sub (integrable_const z) hint, integral_sub hid hint, BNP_int_id]
      simp
      ring
    rw [this]; ring

