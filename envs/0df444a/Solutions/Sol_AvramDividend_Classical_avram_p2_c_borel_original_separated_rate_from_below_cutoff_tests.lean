-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_below_cutoff_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:21:04.530569+00:00
-- url     : https://prove2.me/submissions/151f7bc1-afe3-4e8e-8277-c6039c58db27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_scaled_cutoff_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_marked_mean_from_below_tests_and_cutoff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- True original separated ν rate from below-cutoff dense analytic tests and one cutoff total. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε))
    (D : Set ℝ) (hDense : Dense D)
    (hCut : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (-ε))))
    (hBelow : ∀ a : ℝ, a ∈ D → a < -ε →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic a) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic a))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  let ρ : Measure ℝ := ((t - s : ℝ≥0) : ℝ≥0∞) • X.ν
  have hνfin : X.ν (Iic (-ε)) ≠ ⊤ := by
    exact ne_of_lt
      (avram_p2_a_zero_rate_separated_borel_nu_finite
        X (Iic (-ε)) measurableSet_Iic ε hε (fun y hy => hy))
  have hρfin : ρ (Iic (-ε)) ≠ ⊤ :=
    avram_p2_c_borel_scaled_cutoff_finite X.ν (-ε) hνfin (t - s)
  have hCutρ : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) = ρ (Iic (-ε)) := by
    simpa only [ρ, Measure.smul_apply, smul_eq_mul] using hCut
  have hBelowρ : ∀ a : ℝ, a ∈ D → a < -ε →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic a) ∂P) = ρ (Iic a) := by
    intro a ha hac
    simpa only [ρ, Measure.smul_apply, smul_eq_mul] using hBelow a ha hac
  have hAll :=
    avram_p2_c_borel_original_marked_mean_from_below_tests_and_cutoff
      X s t hst ε hε ρ hρfin D hDense hCutρ hBelowρ B hB
  have hBand : B ∩ Iic (-ε) = B := by
    ext y
    simp only [mem_inter_iff]
    exact ⟨And.left, fun hy => ⟨hy, hBsep hy⟩⟩
  simpa only [hBand, ρ, Measure.smul_apply, smul_eq_mul] using hAll
