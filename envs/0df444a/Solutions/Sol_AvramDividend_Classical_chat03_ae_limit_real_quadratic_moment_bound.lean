-- Prove2me | solution 1 for AvramDividend.Classical.chat03_ae_limit_real_quadratic_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:21:48.467959+00:00
-- url     : https://prove2.me/submissions/c8223a54-b2c4-4928-ab7e-f0af6a199fe4

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_chat03_ae_limit_quadratic_moment_bound
import Theorems.Thm_AvramDividend_Classical_chat03_lintegral_bound_implies_real_integral_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

/-!
The real quadratic moment of the almost-everywhere limit is
integrable and retains the common bound of the approximating sequence.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hZm : AEStronglyMeasurable Z P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)))
    (C : ℝ) (hC : 0 ≤ C)
    (hY2 : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) P ∧
      ∫ ω, (Y n ω) ^ 2 ∂P ≤ C) :
    Integrable (fun ω => (Z ω) ^ 2) P ∧
      (∫ ω, (Z ω) ^ 2 ∂P) ≤ C := by
  have hlin := chat03_ae_limit_quadratic_moment_bound
    P Y Z C hYm hconv hY2
  have hsqm : AEStronglyMeasurable (fun ω => (Z ω) ^ 2) P :=
    (continuous_id.pow 2).comp_aestronglyMeasurable hZm
  have hsq0 : ∀ᵐ ω ∂P, 0 ≤ (Z ω) ^ 2 :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg (Z ω))
  have hfinite : (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
  have hsqi : Integrable (fun ω => (Z ω) ^ 2) P :=
    (lintegral_ofReal_ne_top_iff_integrable hsqm hsq0).mp hfinite
  exact ⟨hsqi, chat03_lintegral_bound_implies_real_integral_bound
    P (fun ω => (Z ω) ^ 2) C hsqi hsq0 hC hlin⟩
