-- Prove2me | solution 1 for AvramDividend.Classical.chat03_ae_limit_quadratic_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T10:05:25.010107+00:00
-- url     : https://prove2.me/submissions/94e769dc-a675-4edd-8356-a147f1eda642

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_fatou_ae_limit_lintegral_le_uniform_bound
import Theorems.Thm_AvramDividend_Classical_chat03_quadratic_moment_lintegral_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

/-!
The uniform quadratic-moment bound passes to an almost-everywhere
real limit via the pinned extended-real Fatou theorem.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (C : ℝ)
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)))
    (hY2 : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) P ∧
      ∫ ω, (Y n ω) ^ 2 ∂P ≤ C) :
    (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≤ ENNReal.ofReal C := by
  have hc : Continuous (fun y : ℝ => ENNReal.ofReal (y ^ 2)) :=
    ENNReal.continuous_ofReal.comp (continuous_id.pow 2)
  have hFm (n : ℕ) :
      AEMeasurable (fun ω => ENNReal.ofReal ((Y n ω) ^ 2)) P :=
    hc.measurable.comp_aemeasurable (hYm n).aemeasurable
  have hlim :
      ∀ᵐ ω ∂P, Tendsto
        (fun n => ENNReal.ofReal ((Y n ω) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((Z ω) ^ 2))) := by
    filter_upwards [hconv] with ω hω
    exact (hc.tendsto (Z ω)).comp hω
  exact chat03_fatou_ae_limit_lintegral_le_uniform_bound P
    (fun n ω => ENNReal.ofReal ((Y n ω) ^ 2))
    (fun ω => ENNReal.ofReal ((Z ω) ^ 2)) (ENNReal.ofReal C)
    hFm hlim (fun n => chat03_quadratic_moment_lintegral_le P (Y n) C (hY2 n))
