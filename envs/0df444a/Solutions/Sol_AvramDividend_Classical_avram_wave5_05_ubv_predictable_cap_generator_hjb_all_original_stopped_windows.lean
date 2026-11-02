-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_predictable_cap_generator_hjb_all_original_stopped_windows
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:55:14.450207+00:00
-- url     : https://prove2.me/submissions/1de14813-9f4d-4d1e-b443-80a4afdc8a4b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_and_secant_admissible_only

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
The original predictable source-generator HJB holds on one
conull event simultaneously in EVERY random stopped window,
including windows that begin at initial or recurrent cap
contact. No permanent stopping at the first contact.
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
    ∀ᵐ ω ∂P, ∀ window : Ω → Set ℝ≥0,
      ∀ᵐ t : ℝ≥0 ∂μ,
        (t ∈ window ω ∧ 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
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
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t - c)) ≤ 0 := by
  have hGen :=
    (avram_wave5_05_ubv_original_predictable_cap_generator_and_secant_admissible_only
      X hBV q w c hc hw_cont hw_smooth hw_gen hw_grad
      x hxc D hD μ).2
  filter_upwards [hGen] with ω hωGen
  intro window
  filter_upwards [hωGen] with t htGen
  intro hWindow
  exact htGen ⟨hWindow.2.1, hWindow.2.2⟩
