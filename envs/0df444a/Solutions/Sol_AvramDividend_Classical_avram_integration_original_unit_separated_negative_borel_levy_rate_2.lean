-- Prove2me | solution 2 for AvramDividend.Classical.avram_integration_original_unit_separated_negative_borel_levy_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:28:05.328158+00:00
-- url     : https://prove2.me/submissions/c480bb6c-8775-4476-b40e-22b005460b4a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_mark_mean_band_finite
import Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_negative_halfline_threshold_rates
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_cutoff_dense_halfline_ext
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original unit marked-jump rates on Borel bands from the genuine mean measure and threshold rates. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = X.ν B := by
  obtain ⟨μ, hμ, hμBand⟩ :=
    avram_p2_a_zero_rate_original_mark_mean_band_finite
      X (1 : ℝ≥0) (by norm_num)
  have hCuts (δ : ℝ) (hδ : 0 < δ) :
      μ (Iic (-δ)) = X.ν (Iic (-δ)) := by
    calc
      μ (Iic (-δ)) =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 (1 : ℝ≥0) ×ˢ Iic (-δ)) ∂P) :=
        hμ _ measurableSet_Iic
      _ = X.ν (Iic (-δ)) :=
        (avram_integration_original_unit_negative_halfline_threshold_rates X δ hδ).1
  have hμfinite : μ (Iic (-ε)) ≠ ⊤ :=
    ne_of_lt (hμBand ε hε)
  have hνfinite : X.ν (Iic (-ε)) ≠ ⊤ :=
    ne_of_lt (avram_p2_a_zero_rate_separated_borel_nu_finite
      X (Iic (-ε)) measurableSet_Iic ε hε (by rfl))
  have hTests : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) →
      μ (Iic a ∩ Iic (-ε)) = X.ν (Iic a ∩ Iic (-ε)) := by
    intro a _
    by_cases ha : a ≤ -ε
    · have hNeg : a < 0 := by linarith
      have hi : Iic a ∩ Iic (-ε) = Iic a :=
        inter_eq_left.mpr (Iic_subset_Iic.mpr ha)
      simpa only [hi, neg_neg] using (hCuts (-a) (by linarith))
    · have ha' : -ε ≤ a := le_of_not_ge ha
      have hi : Iic a ∩ Iic (-ε) = Iic (-ε) :=
        inter_eq_right.mpr (Iic_subset_Iic.mpr ha')
      simpa only [hi] using (hCuts ε hε)
  have hRestriction : μ.restrict (Iic (-ε)) =
      X.ν.restrict (Iic (-ε)) :=
    avram_p2_c_borel_cutoff_dense_halfline_ext
      μ X.ν (-ε) hμfinite hνfinite Set.univ dense_univ hTests
  have hInter : B ∩ Iic (-ε) = B := inter_eq_left.mpr hBsep
  calc
    _ = μ B := (hμ B hB).symm
    _ = (μ.restrict (Iic (-ε))) B := by
      rw [Measure.restrict_apply hB, hInter]
    _ = (X.ν.restrict (Iic (-ε))) B :=
      congrArg (fun κ : Measure ℝ => κ B) hRestriction
    _ = X.ν B := by rw [Measure.restrict_apply hB, hInter]
