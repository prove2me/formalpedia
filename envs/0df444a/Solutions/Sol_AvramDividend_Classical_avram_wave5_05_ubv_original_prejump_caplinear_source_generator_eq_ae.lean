-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_prejump_caplinear_source_generator_eq_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:41:34.945505+00:00
-- url     : https://prove2.me/submissions/e30fe663-22f4-4941-9e6a-a2c746b6d4be

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
No generator evaluation at a cap corner is needed: every actual predictable
pre-event source state is strictly below c a.e. on physical-time clocks,
where the original slope-one source-generator equality is valid.
-/

/-- Exact source cap-linear generator equality at true pre-event states. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        X.generator (fun y => if y ≤ c then w y else w c + (y - c))
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) =
        X.generator w
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by
  have hC0 : ENNReal.ofReal c ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hInside :=
    avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
      X hBV x (ENNReal.ofReal c) hC0 D hD hxc μ
  filter_upwards [hInside] with ω hω
  filter_upwards [hω] with t ht
  intro hPre
  have huC : Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t < c :=
    (ENNReal.ofReal_lt_ofReal_iff hc).mp (ht hPre).2
  exact avram_wave4_04_cap_linear_extension_source_generator_eq_interior
    X w c (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) huC
