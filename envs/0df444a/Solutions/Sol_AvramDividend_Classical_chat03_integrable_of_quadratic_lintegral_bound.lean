-- Prove2me | solution 1 for AvramDividend.Classical.chat03_integrable_of_quadratic_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T10:11:26.508407+00:00
-- url     : https://prove2.me/submissions/575f43f3-d4af-48ae-8999-1d7f08d75b08

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_chat03_integrable_of_integrable_real_square

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

/-!
Finite quadratic extended-real integral implies integrability of a
real-valued strongly measurable variable on a probability space.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZm : AEStronglyMeasurable Z P) (C : ℝ)
    (hbound : (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≤ ENNReal.ofReal C) :
    Integrable Z P := by
  have hsqm : AEStronglyMeasurable (fun ω => (Z ω) ^ 2) P :=
    (continuous_id.pow 2).comp_aestronglyMeasurable hZm
  have hsq0 : ∀ᵐ ω ∂P, 0 ≤ (Z ω) ^ 2 :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg (Z ω))
  have hfinite : (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hsqi : Integrable (fun ω => (Z ω) ^ 2) P :=
    (lintegral_ofReal_ne_top_iff_integrable hsqm hsq0).mp hfinite
  exact chat03_integrable_of_integrable_real_square Z hZm hsqi
