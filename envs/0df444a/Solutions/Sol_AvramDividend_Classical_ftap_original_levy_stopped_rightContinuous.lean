-- Prove2me | solution 1 for AvramDividend.Classical.ftap_original_levy_stopped_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:22:01.205909+00:00
-- url     : https://prove2.me/submissions/28ae3803-adf6-458b-a0e0-cc3ff41aa28b

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
FTAP RightContinuousStoppedMartingale.lean adaptation, commit 8c9c46e1b6e455f7d3069062957d4363879836ce, Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (τ : Ω → WithTop ℝ≥0) :
    ∀ ω t, ContinuousWithinAt
      (MeasureTheory.stoppedProcess X.X τ · ω) (Set.Ici t) t := by
  intro ω t
  by_cases hτTop : τ ω = ⊤
  · have heq : (fun u => MeasureTheory.stoppedProcess X.X τ u ω) =
        fun u => X.X u ω := by
      funext u
      rw [MeasureTheory.stoppedProcess_eq_of_le]
      simp only [hτTop, le_top]
    rw [heq]
    exact X.rightCont ω t
  · lift τ ω to ℝ≥0 using hτTop with s hs
    have heq : (fun u => MeasureTheory.stoppedProcess X.X τ u ω) =
        fun u => X.X (min u s) ω := by
      funext u
      simp only [MeasureTheory.stoppedProcess]
      rw [← hs, ← WithTop.coe_min,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [heq]
    apply (X.rightCont ω (min t s)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (ContinuousAt.continuousWithinAt
        (continuousAt_id.min (continuousAt_const :
          ContinuousAt (fun _ : ℝ≥0 => s) t))).tendsto
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact min_le_min_right s hu

