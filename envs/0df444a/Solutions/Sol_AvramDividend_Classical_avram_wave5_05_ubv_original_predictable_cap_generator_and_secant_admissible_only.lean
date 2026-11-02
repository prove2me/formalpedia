-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_generator_and_secant_admissible_only
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:55:48.892971+00:00
-- url     : https://prove2.me/submissions/05839891-c723-43c3-9ace-6b256f698d50

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_and_global_secant_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
The original admissibility hypothesis itself contains the
same-filtration dividend strategy witness hD.1.1, so the
predictable source generator and inclusive-cap secants need
no redundant extra strategy assumption.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_gen : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    (∀ ω (t : ℝ≥0),
      (t : ℝ≥0∞) < ruinTime X x D ω →
      ∀ a : ℝ, 0 ≤ a → a ≤ riskProcess X x D t ω →
        riskProcess X x D t ω - a ≤
          w (riskProcess X x D t ω) - w a) ∧
    (∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        X.GeneratorIntegrable
          (fun y => if y ≤ c then w y else w c + (y - c))
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator
          (fun y => if y ≤ c then w y else w c + (y - c))
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
        q * (if Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤ c then
          w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else w c + (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t - c)) ≤ 0) := by
  exact
    avram_wave5_05_ubv_original_predictable_cap_generator_and_global_secant_ae
      X hBV q w c hc hw_cont hw_smooth hw_gen hw_grad
      x hxc D hD hD.1.1 μ
