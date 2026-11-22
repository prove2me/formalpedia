-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_initial_event_masked_rightCont_grid_increment_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T20:54:13.104172+00:00
-- url     : https://prove2.me/submissions/c9d0ee89-2613-4114-a0ec-2163f6d57cd9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Eventwise original-X first-order stochastic cancellation at a physical
Lévy grid cell. The event belongs to the right-continuous time-zero sigma
algebra; its indicator is therefore predictable at every grid cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont 0] A)
    (grid : ℕ → ℝ≥0) (i : ℕ)
    (hGrid : grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hHPast : Measurable[(𝓕.rightCont) (grid i)] (H i))
    (hHI : Integrable (H i) P)
    (hXI : Integrable (X.X (grid (i + 1) - grid i)) P) :
    (∫ ω, (if ω ∈ A then H i ω else 0) *
      (X.X (grid (i + 1)) ω - X.X (grid i) ω -
        (∫ η, X.X (grid (i + 1) - grid i) η ∂P)) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hAgrid : MeasurableSet[(𝓕.rightCont) (grid i)] A :=
    𝓕.rightCont.mono (show (0 : ℝ≥0) ≤ grid i from zero_le) A hA
  have hAmeas : MeasurableSet A :=
    (𝓕.rightCont.le 0) A hA
  let H' : ℕ → Ω → ℝ := fun j ω => if ω ∈ A then H j ω else 0
  let κ : Ω → ℕ := fun _ => i + 1
  have hMaskedMeas : Measurable[(𝓕.rightCont) (grid i)] (H' i) := by
    exact hHPast.ite hAgrid measurable_const
  have hWPast : Measurable[(𝓕.rightCont) (grid i)]
      (fun ω => if i < κ ω then H' i ω else 0) := by
    simpa [κ] using hMaskedMeas
  have hMaskedEq : H' i = A.indicator (H i) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [H', Set.indicator, hω]
  have hMaskedI : Integrable (H' i) P := by
    rw [hMaskedEq]
    exact hHI.indicator hAmeas
  have hWI : Integrable
      (fun ω => if i < κ ω then H' i ω else 0) P := by
    simpa [κ] using hMaskedI
  obtain ⟨Y, hYX, hYc, hYσ, hYν⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hYXI :
      Integrable (Y.X (grid (i + 1) - grid i)) P := by
    simpa only [hYX] using hXI
  have hZero :=
    avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
      Y grid i hGrid H' κ hWPast hWI hYXI
  simpa [κ, H', hYX] using hZero

