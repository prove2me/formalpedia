-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_ruin_min_n_esscher_likelihood_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:17:12.281314+00:00
-- url     : https://prove2.me/submissions/272e5678-a280-4d56-ab63-6761ce330b36

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original finite ruin-stop Esscher likelihood has mean one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ) ∂P) = (1 : ℝ) := by
  have hclock := avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  have hbound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    rw [hτeq ω]
    exact hclock.2.1 ω
  exact avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
    X θ hθ τ hτstop n hbound
