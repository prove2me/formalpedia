-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a187_original_stopped_Gaussian_raw_large_tail_real_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:11:00.686867+00:00
-- url     : https://prove2.me/submissions/a54a720a-2786-47f6-9573-556fa56d3a1f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a184_nonnegative_real_expected_L1_zero_of_extended_integral_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a188_original_stopped_Gaussian_raw_tail_lintegral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original stopped raw Gaussian tail converges in expected real L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (η : ℝ) (hη : 0 < η) :
    let Tail : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω then (if η ≤ |r| then r^2 else 0) else 0
    Tendsto (fun m => ∫ ω, Tail m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  classical
  intro Tail
  have hI := avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
    X hν n ρ hρstop η
  change ∀ m, Integrable (Tail m) P at hI
  have hL := avram_ga_a188_original_stopped_Gaussian_raw_tail_lintegral_zero
    X hν hσ n ρ hρstop η hη
  change Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (Tail m ω) ∂P)
    atTop (𝓝 (0 : ℝ≥0∞)) at hL
  have hPos (m : ℕ) : ∀ᵐ ω ∂P, 0 ≤ Tail m ω := by
    filter_upwards [] with ω
    dsimp [Tail]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  exact avram_ga_a184_nonnegative_real_expected_L1_zero_of_extended_integral_zero
    P Tail hI hPos hL
