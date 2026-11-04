-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_generator_joint_L1_to_G_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:51:08.333487+00:00
-- url     : https://prove2.me/submissions/d3ca8af1-746b-4ab0-a078-1e57d3f0af55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Genuine joint original physical generator L¹ gives L¹ of its stopped path-integrated residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (n : ℕ)
    (μ : Measure ℝ≥0) [SFinite μ]
    (hL1 : Integrable
      (fun p : ℝ≥0 × Ω =>
        if 0 < p.1 ∧ (p.1 : ℝ≥0∞) <
          min (ruinTime X x D p.2) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
        else 0) (μ.prod P)) :
    Integrable (fun ω =>
      ∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0 ∂μ) P := by
  exact hL1.integral_prod_right
