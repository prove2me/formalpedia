-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_undiscounted_joint_L1_to_discounted_G_L1_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:26:59.597132+00:00
-- url     : https://prove2.me/submissions/6491b9ea-e5b9-4d19-85c3-01f4ca7c92e4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_clock_discounted_joint_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_discounted_exact_clock_G_L1_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Exact original discounted generator has a globally L¹, nonpositive source residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (n : ℕ) (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (hL1 : Integrable (fun p : ℝ≥0 × Ω =>
      if 0 < p.1 ∧ (p.1 : ℝ≥0∞) <
          min (ruinTime X x D p.2) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
        else 0) (μ.prod P)) :
    Integrable (fun ω =>
      ∫ t : ℝ≥0,
        Real.exp (-(q * (t : ℝ))) * (if 0 < t ∧ (t : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0) ∂μ) P ∧
    ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0,
        Real.exp (-(q * (t : ℝ))) * (if 0 < t ∧ (t : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0) ∂μ) ≤ 0 := by
  have hDiscount :=
    avram_p4_e_localise_original_exact_clock_discounted_joint_L1
      X x D w q hq n μ hL1
  exact avram_p4_e_localise_original_discounted_exact_clock_G_L1_nonpositive
    P X hBV x C hC0 D hD hxc w q hwGen n μ hDiscount
