-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_stop_original_Q_ceiling_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:47:00.579639+00:00
-- url     : https://prove2.me/submissions/7bd6b66e-a815-4b28-8a16-b090ef5dc045

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_zerojump_ceiling_path_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Physical Gaussian compensated squares converge along any original-source
ceiling approaching a possibly random stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (grid : ℕ → ℕ → ℝ≥0) (K : ℕ → Ω → ℕ)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (nhds 0))
    (hBounds : ∀ n ω,
      σ ω ≤ grid n (K n ω) ∧
      grid n (K n ω) ≤ σ ω + δ n) :
    ∀ᵐ ω ∂P, Tendsto (fun n =>
      (X.X (grid n (K n ω)) ω -
        (grid n (K n ω) : ℝ) * X.c) ^ 2 -
        (grid n (K n ω) : ℝ) * X.σ ^ 2)
      atTop (nhds
        ((X.X (σ ω) ω - (σ ω : ℝ) * X.c) ^ 2 -
          (σ ω : ℝ) * X.σ ^ 2)) := by
  filter_upwards [
    avram_ubv_finite12_original_zerojump_ceiling_path_limit
      X hν σ grid K δ hδ hBounds] with ω hPath
  have hUpper : Tendsto (fun n => σ ω + δ n) atTop (nhds (σ ω)) := by
    simpa using (tendsto_const_nhds.add hδ :
      Tendsto (fun n => σ ω + δ n) atTop (nhds (σ ω + 0)))
  have hTimes : Tendsto (fun n => grid n (K n ω)) atTop (nhds (σ ω)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hUpper
      (fun n => (hBounds n ω).1)
      (fun n => (hBounds n ω).2)
  have hReal : Tendsto (fun n => (grid n (K n ω) : ℝ))
      atTop (nhds (σ ω : ℝ)) :=
    (NNReal.continuous_coe.tendsto (σ ω)).comp hTimes
  have hM := hPath.sub (hReal.mul_const X.c)
  have hQ := (hM.pow 2).sub (hReal.mul_const (X.σ ^ 2))
  simpa only [] using hQ
