-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_prejump_source_mass_tail_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T18:56:36.158802+00:00
-- url     : https://prove2.me/submissions/6eccdece-2048-47d8-bbfa-26a0fdc449b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_measurable_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_tail_L1_any_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original pre-jump reserve clipping has an L1-negligible complement
under the genuine integrable bounded-variation source-mass envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤)
    (T : ℝ≥0) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ N : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, s n = {ω | ∀ i ∈ Finset.range (n + 1),
        abs (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
          (u n i)) ≤ (N n : ℝ)}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) ∧
      (∀ n, Integrable (fun ω => if ω ∈ s n then 0 else
        K₀ * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) P) ∧
      Tendsto (fun n => ∫ ω, if ω ∈ s n then 0 else
        K₀ * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P)
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨N, s, hs_def, hs_meas, hs_eventual⟩ :=
    avram_bv_residual10_original_prejump_measurable_exhaustion
      (P := P) X x D hD u ε hεpos hεlim hεsum
  obtain ⟨h_int, h_lim⟩ :=
    avram_p3_comp8_original_BV_source_tail_L1_any_clock
      X hX hBV T K₀ hK₀ s hs_meas hs_eventual
  exact ⟨N, s, hs_def, hs_meas, hs_eventual, h_int, h_lim⟩
