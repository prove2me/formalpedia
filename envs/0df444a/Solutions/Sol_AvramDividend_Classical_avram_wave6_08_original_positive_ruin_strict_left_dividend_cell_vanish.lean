-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_ruin_strict_left_dividend_cell_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:49:57.095349+00:00
-- url     : https://prove2.me/submissions/e610995c-48d9-4431-9029-c2810e6abae6

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.NhdsWithin
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The final strictly pre-ruin dividend cell vanishes without counting a
right-hand dividend at the positive ruin instant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : ℝ≥0) (hτ : 0 < τ)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < τ)
    (hlim : Tendsto u atTop (𝓝 τ)) :
    Tendsto (fun n => D τ ω - rightLimit D (u n) ω) atTop (𝓝 0) := by
  have huWithin : Tendsto u atTop (𝓝[<] τ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hlim, Filter.Eventually.of_forall hu⟩
  have hvalue :
      Tendsto (fun n => rightLimit D (u n) ω) atTop (𝓝 (D τ ω)) :=
    (avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD ω τ hτ).comp huWithin
  have hsub :
      Tendsto (fun n => D τ ω - rightLimit D (u n) ω)
        atTop (𝓝 (D τ ω - D τ ω)) :=
    tendsto_const_nhds.sub hvalue
  simpa only [sub_self] using hsub
