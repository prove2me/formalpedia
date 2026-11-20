-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_true_positive_clock_expected_source_le_bias_from_zero_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:56:16.31919+00:00
-- url     : https://prove2.me/submissions/e07c99e3-35de-40c2-a98b-dc918560d572

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_centered_source_expected_upper_by_bias
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (hσmeas : Measurable σ) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (Source M Q : ℕ → Ω → ℝ) (bias : ℕ → ℝ)
    (hQphysical : ∀ j ω,
      Q j ω = (let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
        let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
        let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
        ∑ i ∈ Finset.range (m j),
          E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
            (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
              X.generator w (Y (v i)) - q * w (Y (v i))
             else 0)))
    (hM : ∀ j, Integrable (M j) P)
    (hQ : ∀ j, Integrable (Q j) P)
    (hMzero : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hSource : ∀ j ω, Source j ω = M j ω + Q j ω + bias j)
    (hZero : ∀ j ω, σ ω = 0 → Source j ω = 0) :
    ∀ j, (∫ ω in {ω | 0 < σ ω}, Source j ω ∂P) ≤ bias j := by
  classical
  intro j
  have hGlobal : (∫ ω, Source j ω ∂P) ≤ bias j :=
    avram_jump6_B_original_physical_centered_source_expected_upper_by_bias
      X q w C hw_gen x D σ u m Source M Q bias
      hQphysical hM hQ hMzero hSource j
  let A : Set Ω := {ω : Ω | 0 < σ ω}
  have hA : MeasurableSet A := by
    have hPre : MeasurableSet (σ ⁻¹' Set.Ioi (0 : ℝ≥0)) :=
      measurableSet_Ioi.preimage hσmeas
    exact hPre
  have hIdent : ∀ ω, A.indicator (Source j) ω = Source j ω := by
    intro ω
    by_cases hp : 0 < σ ω
    · simp [A, Set.indicator_of_mem hp]
      intro hz
      exact (ne_of_gt hp hz).elim
    · have hz : σ ω = 0 :=
        le_antisymm (le_of_not_gt hp) (show 0 ≤ σ ω from zero_le)
      simp [A, Set.indicator_of_notMem hp, hZero j ω hz]
  calc
    (∫ ω in A, Source j ω ∂P) =
        ∫ ω, A.indicator (Source j) ω ∂P :=
      (integral_indicator hA).symm
    _ = ∫ ω, Source j ω ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hIdent)
    _ ≤ bias j := hGlobal
