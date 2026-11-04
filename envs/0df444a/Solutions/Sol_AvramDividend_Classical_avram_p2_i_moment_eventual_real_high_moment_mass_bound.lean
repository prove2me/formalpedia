-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_eventual_real_high_moment_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:53:15.09789+00:00
-- url     : https://prove2.me/submissions/5dda738c-a884-485a-a417-176c5e2e5143

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_real_unit_high_moment_le_mass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    {ι : Type*} (l : Filter ι) (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hμ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hOne : Integrable (fun _ : ℝ => (1 : ℝ)) μ)
    (k : ℕ) (hk : Integrable (fun z : ℝ => z ^ k) μ)
    (hmom : Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
      (nhds (∫ z : ℝ, z ^ k ∂μ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in l, (∫ z : ℝ, z ^ k ∂μi i) <
      (∫ _ : ℝ, (1 : ℝ) ∂μ) + ε := by
  have hbound :=
    AvramDividend.Classical.avram_p2_i_moment_real_unit_high_moment_le_mass
      μ hμ hOne k hk
  have hstrict :
      (∫ z : ℝ, z ^ k ∂μ) <
        (∫ _ : ℝ, (1 : ℝ) ∂μ) + ε := by
    linarith
  exact hmom.eventually (eventually_lt_nhds hstrict)
