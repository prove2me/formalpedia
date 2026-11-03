-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_negative_large_mark_discounted_levy_L1_on_true_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:32:39.791586+00:00
-- url     : https://prove2.me/submissions/17be0ddc-19e1-4dbc-b621-201e436a570e

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Negative marks separated from zero are integrable for the actual
controlled C1 candidate because the true Levy tail has finite physical mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b R : ℝ) (ha : 0 < a) (hab : a ≤ b) (hR : 0 ≤ R)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (hMeas : AEStronglyMeasurable (fun z : ℝ =>
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t + z) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t)))
      (X.ν.restrict (Iic (-a / 2)))) :
    IntegrableOn (fun z : ℝ =>
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t + z) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t)))
      (Iic (-a / 2)) X.ν := by
  apply MeasureTheory.IntegrableOn.of_bound hMass hMeas (2 * R)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with z hz
  have hPoint :=
    avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
      X x D w q hq a b R ha hab hR hWbound ω t hBand z hz
  simpa only [Real.norm_eq_abs] using hPoint
