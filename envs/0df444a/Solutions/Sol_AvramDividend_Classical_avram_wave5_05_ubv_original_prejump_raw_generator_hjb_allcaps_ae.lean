-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_prejump_raw_generator_hjb_allcaps_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:37:49.545375+00:00
-- url     : https://prove2.me/submissions/fa73ded6-a8ce-4db5-9dbc-e77fbab9f5f6

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
The actual original predictable pre-event reserve is in the strict HJB
generator domain a.e. on atomless physical-time clocks, for every nonzero cap.
-/

/-- Original pre-event Lévy generator is integrable and HJB-nonpositive a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        X.GeneratorIntegrable w
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
        q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ 0 := by
  have hInside :=
    avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
      X hBV x C hC0 D hD hxc μ
  filter_upwards [hInside] with ω hω
  filter_upwards [hω] with t ht
  intro hPre
  exact hw_gen _ (ht hPre).1 (ht hPre).2
