-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_dense_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:46:05.109929+00:00
-- url     : https://prove2.me/submissions/a2bad569-4ab0-4b15-a6a8-71022ac26343

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_marked_mean_ext_of_dense_tests_no_finite_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Conditional original separated ν rate reduces to analytically proved dense halfline identities. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε))
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic a ∩ Iic (-ε)))) :
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
  have hρfin : ρ (Iic (-ε)) ≠ ⊤ := by
    have hT : (((t - s : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
    simpa only [ρ, Measure.smul_apply, smul_eq_mul] using
      (ENNReal.mul_ne_top hT hνfin)
  have hDenseρ : ∀ a : ℝ, a ∈ D →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) = ρ (Iic a ∩ Iic (-ε)) := by
    intro a ha
    simpa only [ρ, Measure.smul_apply, smul_eq_mul] using hTests a ha
  have hAll :=
    avram_p2_c_borel_original_marked_mean_ext_of_dense_tests_no_finite_mean
      X s t hst ε hε ρ hρfin D hDense hDenseρ B hB
  have hBand : B ∩ Iic (-ε) = B := by
    ext y
    simp only [mem_inter_iff]
    exact ⟨And.left, fun hy => ⟨hy, hBsep hy⟩⟩
  simpa only [hBand, ρ, Measure.smul_apply, smul_eq_mul] using hAll
