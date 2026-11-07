-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_positive_error_event_tail_absorption
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:41:22.964955+00:00
-- url     : https://prove2.me/submissions/59c178d1-440b-4ea9-9021-5b6a16f44412

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_mass_exhaustion_L1_tail
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_fixed_event_uniform_tail_absorption
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Metric AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The actual BV source-mass tail gives the uniform-in-grid positive
error complement estimate needed by fixed-event Fatou absorption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1)
    (K : ℝ) (hK : 0 ≤ K)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n)
    (Err : ℕ → Ω → ℝ)
    (hPos : ∀ m, Integrable (fun ω => max (Err m ω) 0) P)
    (hLocal : ∀ n, Tendsto
      (fun m => ∫ ω, max (if ω ∈ s n then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hOutside : ∀ n m, ∀ᵐ ω ∂P, ω ∉ s n →
      max (Err m ω) 0 ≤
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  let tail : ℕ → ℝ := fun n =>
    ∫ ω, if ω ∈ s n then 0 else
      K * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) ∂P
  obtain ⟨hTailInt, hTailZero⟩ :=
    avram_bv_error7_original_BV_source_mass_exhaustion_L1_tail
      X hX hBV T hT K hK s hs hExhaust
  have hTailBound (n m : ℕ) :
      (∫ ω, max (if ω ∉ s n then Err m ω else 0) 0 ∂P) ≤ tail n := by
    have hIndicator :
        (fun ω => max (if ω ∉ s n then Err m ω else 0) 0) =
          (s n)ᶜ.indicator (fun ω => max (Err m ω) 0) := by
      funext ω
      by_cases hω : ω ∈ s n <;>
        simp [Set.indicator, hω]
    have hIntegrable :
        Integrable
          (fun ω => max (if ω ∉ s n then Err m ω else 0) 0) P := by
      rw [hIndicator]
      exact (hPos m).indicator (hs n).compl
    have hOrder :
        ∀ᵐ ω ∂P,
          max (if ω ∉ s n then Err m ω else 0) 0 ≤
          (if ω ∈ s n then 0 else
            K * (|X.drift| * (T : ℝ) +
              |(T : ℝ) * X.drift - X.X T ω|)) := by
      filter_upwards [hOutside n m] with ω hω
      by_cases hωs : ω ∈ s n
      · simp [hωs]
      · simpa [hωs] using hω hωs
    exact integral_mono_ae hIntegrable (hTailInt n) hOrder
  exact avram_bv_error7_fixed_event_uniform_tail_absorption
    P s hs Err hPos hLocal tail hTailZero hTailBound
