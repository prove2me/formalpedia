-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_ruin_min_n_esscher_density_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:09:21.425712+00:00
-- url     : https://prove2.me/submissions/567f8cc8-fc6e-4762-98b3-7959c500f675

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_density_probability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original ruin-truncated clock supports its original Esscher density. -/
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
    IsProbabilityMeasure (P.withDensity (fun ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) := by
  have hclock := avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  have hbound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    rw [hτeq ω]
    exact hclock.2.1 ω
  exact avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_density_probability
    X θ hθ τ hτstop n hbound
