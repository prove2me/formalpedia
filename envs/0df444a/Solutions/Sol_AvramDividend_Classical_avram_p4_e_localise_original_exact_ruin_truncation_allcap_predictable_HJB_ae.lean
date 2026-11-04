-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_exact_ruin_truncation_allcap_predictable_HJB_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:47:57.285757+00:00
-- url     : https://prove2.me/submissions/202239dc-7f37-447a-8741-9793ec4e2fea

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
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
/-- At all exact finite original ruin clocks, original predictable HJB holds on a common P-conull set. -/
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
      0 < t →
      (t : ℝ≥0∞) <
        (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) →
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
  filter_upwards [hω] with t ht
  intro ht0 hBefore
  have hClock :=
    avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  have hBeforeRuin : (t : ℝ≥0∞) < ruinTime X x D ω :=
    lt_of_lt_of_le hBefore (hClock.2.2 ω)
  have hInt := ht ⟨ht0, hBeforeRuin⟩
  exact hwGen _ hInt.1 hInt.2
