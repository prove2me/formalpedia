-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_signed_mesh_vanishing_bias_eventual_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:06:02.874683+00:00
-- url     : https://prove2.me/submissions/d2f84ebb-185f-41ce-9fbc-f5f60589bbd3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*}
    (Source M Q : ℕ → Ω → ℝ) (bias : ℕ → ℝ)
    (hSource : ∀ j ω, Source j ω = M j ω + Q j ω + bias j)
    (hQsign : ∀ j ω, Q j ω ≤ 0)
    (hBias : Tendsto bias atTop (𝓝 (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ ω, Source j ω ≤ M j ω + ε := by
  intro ε hε
  have hmem : (0 : ℝ) ∈ Iio ε := hε
  filter_upwards [hBias.eventually (isOpen_Iio.mem_nhds hmem)]
    with j hj
  intro ω
  rw [hSource j ω]
  have hSign := hQsign j ω
  have hSmall : bias j < ε := hj
  linarith
