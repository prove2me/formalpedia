-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_exact_inclusive_clock_atomless_predictable_HJB_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T11:02:08.521795+00:00
-- url     : https://prove2.me/submissions/599f3082-1461-4815-8057-39ad9211f2b7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Inclusion of the finite ruin horizon does not alter physical-time predictable HJB almost everywhere. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ t : ℝ≥0 ∂μ,
      t ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal →
      X.GeneratorIntegrable w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) - q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ 0 := by
  have hInterior :=
    avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
      X hBV x C hC0 D hD hxc μ
  filter_upwards [hInterior] with ω hω
  intro n
  have hClock :=
    avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  filter_upwards [hω, μ.ae_ne (0 : ℝ≥0),
      μ.ae_ne ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)]
    with t ht htZero htEnd
  intro hLe
  have htPos : 0 < t := lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from zero_le) (Ne.symm htZero)
  have htStrict : t < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal :=
    lt_of_le_of_ne hLe htEnd
  have htClock : (t : ℝ≥0∞) <
      (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.mpr htStrict
  have htRuin : (t : ℝ≥0∞) < ruinTime X x D ω :=
    lt_of_lt_of_le htClock (hClock.2.2 ω)
  have hInt := ht ⟨htPos, htRuin⟩
  exact hwGen _ hInt.1 hInt.2