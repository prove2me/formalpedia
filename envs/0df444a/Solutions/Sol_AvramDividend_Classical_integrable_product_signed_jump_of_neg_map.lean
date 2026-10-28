-- Prove2me | solution 1 for AvramDividend.Classical.integrable_product_signed_jump_of_neg_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:42:19.554705+00:00
-- url     : https://prove2.me/submissions/40d2f4a5-a015-454f-865c-d4eb46227246

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Pull back product integrability through reflection of the second coordinate. -/
theorem solution
    (μ ν : Measure ℝ) [SFinite ν]
    (F G : ℝ × ℝ → ℝ)
    (hF : Integrable F (μ.prod (ν.map (fun y : ℝ => -y))))
    (hFG : (F ∘ Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y))
      =ᵐ[μ.prod ν] G) :
    Integrable G (μ.prod ν) := by
  have hmeas : Measurable
      (Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y)) :=
    measurable_id.prodMap measurable_neg
  have hmap :
      μ.prod (ν.map (fun y : ℝ => -y)) =
        Measure.map (Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y))
          (μ.prod ν) := by
    ext s hs
    rw [Measure.prod_apply hs]
    rw [Measure.map_apply hmeas hs]
    rw [Measure.prod_apply (hs.preimage hmeas)]
    apply lintegral_congr
    intro x
    have hsection : MeasurableSet {y : ℝ | (x, y) ∈ s} :=
      hs.preimage (measurable_const.prodMk measurable_id)
    exact Measure.map_apply measurable_neg hsection
  have hFmap : Integrable F
      (Measure.map (Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y))
        (μ.prod ν)) := by
    rw [← hmap]
    exact hF
  exact (hFmap.comp_measurable hmeas).congr hFG
