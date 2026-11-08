-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen11_original_BV_drift_dividend_cap_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:30:15.33694+00:00
-- url     : https://prove2.me/submissions/793c61ab-c002-4f95-8009-dc3a345a4b85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_all_times
import Theorems.Thm_AvramDividend_Classical_avram_gen10_drift_cancelled_dividend_cap_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- The actual BV Lévy drift bound gives the dividend cap on one full-measure event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hb : 0 ≤ X.drift) (x T : ℝ)
    (s : Ω → ℝ≥0) (A : Ω → ℝ) (hA : ∀ ω, 0 ≤ A ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      x + X.X t ω -
        ((if s ω < t then A ω else 0) +
          X.drift * max ((t : ℝ) - T) 0) ≤ x + X.drift * T := by
  filter_upwards [bv_actual_levy_drift_upper_ae_all_times X hBV] with ω hω
  have hpath : ∀ t (u : Unit), X.X t ω ≤ X.drift * (t : ℝ) := by
    intro t u
    simpa only [mul_comm] using hω t
  have hpayout : ∀ u : Unit, 0 ≤ (fun _ : Unit => A ω) u := by
    intro u
    exact hA ω
  have hcap := avram_gen10_drift_cancelled_dividend_cap_bound
    (fun t (_ : Unit) => X.X t ω) X.drift x T hb
    (fun _ : Unit => s ω) (fun _ : Unit => A ω) hpayout hpath
  intro t
  exact hcap () t
