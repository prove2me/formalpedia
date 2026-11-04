-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_expected_measure_sigma_finite_additive_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:26:20.59626+00:00
-- url     : https://prove2.me/submissions/f2e9c90b-bd3a-4b5f-881a-73635f0a2ab9

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_additive_mean_measure_negative_support
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_expected_mark_measure_sigma_finite_all_horizons
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A single original expected marked-count measure family satisfies the
additive, negative-support and sigma-finiteness properties simultaneously. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ μ : ℝ≥0 → Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        μ T B =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∀ s t : ℝ≥0, μ (s + t) = μ s + μ t) ∧
      (∀ ε : ℝ, 0 < ε → μ 1 (Iic (-ε)) < ⊤) ∧
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        μ T B = μ T (B ∩ Iio (0 : ℝ))) ∧
      (∀ T : ℝ≥0, SigmaFinite (μ T)) := by
  obtain ⟨μ, hRep, hAdd, hFin, hSupp⟩ :=
    avram_p2_c_borel_original_additive_mean_measure_negative_support X
  obtain ⟨η, hRepη, hSigmaη⟩ :=
    avram_p2_c_borel_original_expected_mark_measure_sigma_finite_all_horizons X
  have hEq : μ = η := by
    funext T
    apply Measure.ext
    intro B hB
    exact (hRep T B hB).trans (hRepη T B hB).symm
  refine ⟨μ, hRep, hAdd, hFin, hSupp, ?_⟩
  intro T
  rw [hEq]
  exact hSigmaη T
