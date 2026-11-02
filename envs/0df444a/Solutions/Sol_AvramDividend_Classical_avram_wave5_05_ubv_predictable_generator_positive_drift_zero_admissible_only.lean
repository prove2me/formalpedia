-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_predictable_generator_positive_drift_zero_admissible_only
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:46:17.801429+00:00
-- url     : https://prove2.me/submissions/975ac6f8-7a33-4e7b-a348-fed6fe0c6c50

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_positive_drift_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
No redundant strategy hypothesis: genuine capped admissibility
already supplies the same-filtration strategy hD.1.1. The
actual predictable cap-generator positive drift has zero
integrated mass on every fixed atomless physical-time clock.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_gen : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        ENNReal.ofReal
          (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
            X.generator
              (fun y => if y ≤ c then w y else w c + (y - c))
              (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
              q * (if Function.leftLim
                    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤ c then
                w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
              else w c + (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t - c))
          else 0) ∂μ) = 0 := by
  exact
    avram_wave5_05_ubv_original_predictable_cap_generator_positive_drift_zero
      X hBV q w c hc hw_gen x hxc D hD hD.1.1 μ
