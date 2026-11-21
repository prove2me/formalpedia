-- Prove2me | solution 1 for AvramDividend.Classical.avram_a34b_original_zerojump_fullband_true_crossing_uniform_integrable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:15:50.98714+00:00
-- url     : https://prove2.me/submissions/ba00211a-e070-49b0-8965-b41ff89ed2f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_gaussian_bounded_horizon_all_increments_integrable_majorant
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hwcont : ContinuousOn w (Set.Ici 0))
    (hwneg : ∀ z : ℝ, z < 0 → w z = 0)
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc 0 c) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, 0 ≤ B ω ∧ ∀ m,
        max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
           then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
           else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
           w (y m ω)) 0 ≤ B ω)  := by
  obtain ⟨K, hK, hV⟩ :=
    avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
      w c hc hwcont hwneg
  obtain ⟨B0, hBI, hBound⟩ :=
    avram_a28_original_gaussian_bounded_horizon_all_increments_integrable_majorant
      X hν T
  let B : Ω → ℝ := fun ω => K + c + B0 ω
  have hBI' : Integrable B P := by
    dsimp [B]
    exact (integrable_const (K + c)).add hBI
  refine ⟨B, hBI', ?_⟩
  filter_upwards [hy, hRange, hBound] with ω hY hR hB
  constructor
  · dsimp [B]
    linarith [hB.1]
  · intro m
    let z : ℝ := X.X (t m ω) ω - X.X (s m ω) ω
    let v : ℝ :=
      (if y m ω + z ≤ c then w (y m ω + z)
       else w c + (y m ω + z - c)) - w (y m ω)
    have hZ : |z| ≤ B0 ω := by
      exact hB.2 (s m ω) (t m ω) (hR m).1.2 (hR m).2.2
    have hVbd : |v| ≤ K + c + |z| := by
      simpa only [v] using hV (y m ω) z (hY m).1 (hY m).2
    have hmax : max v 0 ≤ |v| :=
      max_le (le_abs_self v) (abs_nonneg v)
    change max v 0 ≤ B ω
    dsimp [B]
    linarith
