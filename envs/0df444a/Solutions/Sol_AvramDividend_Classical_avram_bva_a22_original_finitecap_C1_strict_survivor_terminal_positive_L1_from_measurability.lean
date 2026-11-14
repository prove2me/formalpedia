-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_finitecap_C1_strict_survivor_terminal_positive_L1_from_measurability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:03.733524+00:00
-- url     : https://prove2.me/submissions/97f34d17-50b7-4859-9d7e-ed8b622524e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_finitecap_strict_survival_both_endpoints_closed_clipped_band
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_candidate_zero_boundary_uniform_modulus
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_survivor_terminal_positive_omission_integrable_from_measurability
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_survivor_closedband_discounted_terminal_positive_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (C : ℝ≥0∞) (hC : 0 < C)
    (hCfinite : C ≠ ⊤) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ))) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (x + X.X t ω - rightLimit D t ω))
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ m, AEStronglyMeasurable (Err m) P) →
    Tendsto (fun m => ∫ ω, Err m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  intro S Err hErrMeas
  letI : IsProbabilityMeasure P := X.isProbability
  have hDs : IsDividendStrategy 𝓕 D := hD.1.1
  let B : ℝ := min (x + T * X.drift) C.toReal
  have hEnds :=
    avram_bva_a22_original_BV_finitecap_strict_survival_both_endpoints_closed_clipped_band
      X hX hBV x C hxc hCfinite D hD T hT u huniform
  have hMono : MonotoneOn w (Icc (0 : ℝ) B) :=
    avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
      C hC w hw_cont hw_smooth hw_grad B
      (Or.inr (min_le_right _ _))
  have hMod :=
    avram_bva_a22_original_candidate_zero_boundary_uniform_modulus
      w B hw_cont
  have hInt :=
    avram_bva_a22_original_survivor_terminal_positive_omission_integrable_from_measurability
      X hX hBV q hq w hw_cont x D hDs hw_nonneg T hT u huniform
      hErrMeas
  exact avram_bva_a22_original_BV_survivor_closedband_discounted_terminal_positive_L1
    X hBV x D hDs w q (le_of_lt hq) B hw0
    hMono hMod T hT u huniform hEnds hInt
