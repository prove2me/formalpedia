-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_nonnegative_reserve_limit_compose_continuous_w
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:16:08.7906+00:00
-- url     : https://prove2.me/submissions/e835b786-b185-49ae-adc0-df4d36bab647

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (f : ℕ → ℝ) (y : ℝ)
    (hy : 0 ≤ y)
    (hf : Tendsto f atTop (𝓝 y))
    (hpos : ∀ᶠ m : ℕ in atTop, 0 ≤ f m) :
    Tendsto (fun m => w (f m)) atTop (𝓝 (w y)) := by
  have hwithin : Tendsto f atTop (𝓝[Set.Ici 0] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hf, hpos⟩
  have hw : ContinuousWithinAt w (Ici 0) y := hw_cont y hy
  simpa only [Function.comp_def] using hw.tendsto.comp hwithin
