-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_centred_ceiling_path_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:05:21.706701+00:00
-- url     : https://prove2.me/submissions/95dea0ae-afca-41c2-9e9a-9f0a25b95654

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_zerojump_ceiling_path_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The original centred Gaussian source converges along true physical grid
ceilings that approach the original random stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (grid : ℕ → ℕ → ℝ≥0) (K : ℕ → Ω → ℕ)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (hBounds : ∀ n ω,
      τ ω ≤ grid n (K n ω) ∧
      grid n (K n ω) ≤ τ ω + δ n) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n =>
        X.X (grid n (K n ω)) ω -
          (grid n (K n ω) : ℝ) * X.c)
        atTop (𝓝 (X.X (τ ω) ω - (τ ω : ℝ) * X.c)) := by
  filter_upwards [
    avram_ubv_finite12_original_zerojump_ceiling_path_limit
      X hν τ grid K δ hδ hBounds] with ω hPath
  have hUpper : Tendsto (fun n => τ ω + δ n) atTop (𝓝 (τ ω)) := by
    simpa using (tendsto_const_nhds.add hδ :
      Tendsto (fun n => τ ω + δ n) atTop (𝓝 (τ ω + 0)))
  have hTimes : Tendsto (fun n => grid n (K n ω)) atTop (𝓝 (τ ω)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hUpper
      (fun n => (hBounds n ω).1)
      (fun n => (hBounds n ω).2)
  have hReal : Tendsto (fun n => (grid n (K n ω) : ℝ))
      atTop (𝓝 (τ ω : ℝ)) :=
    (NNReal.continuous_coe.tendsto (τ ω)).comp hTimes
  simpa only [] using hPath.sub (hReal.mul_const X.c)
