-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb32_original_linear_source_horizon_no_negative_jump_leftLim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:25:38.765348+00:00
-- url     : https://prove2.me/submissions/5cc20702-6241-4650-b986-490016f65643

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S : ℝ≥0)
    (hSource : ∀ t : ℝ≥0, t ≤ S →
      X.X t ω = (t : ℝ) * X.drift) :
    ∀ t : ℝ≥0, t ≤ S →
      X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = 0  := by
  intro t ht
  have hcont : Continuous (fun s : ℝ≥0 => (s : ℝ) * X.drift) := by
    fun_prop
  have hEq : ∀ s ∈ Iic t,
      X.X s ω = (s : ℝ) * X.drift := by
    intro s hs
    exact hSource s (hs.trans ht)
  have hWithin : ContinuousWithinAt (fun s : ℝ≥0 => X.X s ω)
      (Iic t) t :=
    hcont.continuousWithinAt.congr hEq (hSource t ht)
  have hlim := hWithin.leftLim_eq
  rw [hlim]
  exact sub_self _
