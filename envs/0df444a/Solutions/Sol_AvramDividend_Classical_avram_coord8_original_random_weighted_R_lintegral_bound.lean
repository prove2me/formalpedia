-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord8_original_random_weighted_R_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:21:03.085673+00:00
-- url     : https://prove2.me/submissions/435171c2-f3c7-41b2-86ab-c2f610670685

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_coord8_original_random_weighted_R_ae_mesh_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The pointwise original BV remainder envelope passes to the upper integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (a : Ω → ℕ → ℝ) (K : ℝ)
    (hK : ∀ ω i, i ∈ Finset.range (n + 1) → |a ω i| ≤ K) :
    let R : Ω → ℝ≥0 → ℝ := fun ω t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
    (∫⁻ ω, ENNReal.ofReal
      |∑ i ∈ Finset.range (n + 1),
        a ω i * (R ω (u n i) - R ω (u n (i + 1)))| ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal
        (K * (R ω (u n (n + 1)) - R ω (u n 0))) ∂P) := by
  intro R
  apply lintegral_mono_ae
  filter_upwards
    [avram_coord8_original_random_weighted_R_ae_mesh_envelope
      X hBV u n hu a K hK] with ω hω
  exact ENNReal.ofReal_le_ofReal hω
