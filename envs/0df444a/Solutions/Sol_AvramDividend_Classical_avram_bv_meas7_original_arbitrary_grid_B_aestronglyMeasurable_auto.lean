-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:09:16.741835+00:00
-- url     : https://prove2.me/submissions/b80f3546-74b1-4994-882f-1407e88cc7c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_BV_generator_borel_gridfree
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_of_generator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original BV generator and raw-jump residual are AE measurable on any deterministic grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (u : ℕ → ℕ → ℝ≥0) :
    ∀ n, AEStronglyMeasurable (fun ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
          else 0) * (R (u n i) - R (u n (i + 1))))) P := by
  have hw : Measurable w :=
    avram_p3_e_compensator_original_ruin_extension_value_measurable
      w hw_cont hw_neg
  have hGen : Measurable (fun y : ℝ => X.generator w y) :=
    avram_bv_meas7_original_BV_generator_borel_gridfree X hBV w hw
  exact avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_of_generator
    X hX hBV q w hw hGen C x D hD u
