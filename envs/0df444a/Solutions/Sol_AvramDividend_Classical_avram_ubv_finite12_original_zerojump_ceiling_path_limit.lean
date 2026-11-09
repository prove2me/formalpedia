-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite12_original_zerojump_ceiling_path_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:38:16.4992+00:00
-- url     : https://prove2.me/submissions/df9e3dde-d5a3-43cf-b627-f3ab0266a472

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The actual zero-jump source evaluated at arbitrarily chosen nearby
physical grid ceilings converges almost surely at every random clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (grid : ℕ → ℕ → ℝ≥0) (K : ℕ → Ω → ℕ)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (nhds 0))
    (hBounds : ∀ n ω,
      σ ω ≤ grid n (K n ω) ∧ grid n (K n ω) ≤ σ ω + δ n) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (grid n (K n ω)) ω)
        atTop (nhds (X.X (σ ω) ω)) := by
  filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae X hν]
    with ω hcont
  have hUpper : Tendsto (fun n => σ ω + δ n) atTop (nhds (σ ω)) := by
    simpa using (tendsto_const_nhds.add hδ :
      Tendsto (fun n => σ ω + δ n) atTop (nhds (σ ω + 0)))
  have hTimes : Tendsto (fun n => grid n (K n ω)) atTop (nhds (σ ω)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hUpper
      (fun n => (hBounds n ω).1)
      (fun n => (hBounds n ω).2)
  exact hcont.continuousAt.tendsto.comp hTimes
