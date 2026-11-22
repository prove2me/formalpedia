-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_stopped_postdividend_reserve_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:43:21.883799+00:00
-- url     : https://prove2.me/submissions/de4dbafc-0e0f-4036-9827-5b618ce61d4c

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adapted from FTAPTheorem42 right-continuous stopped process.
Commit 8c9c46e1b6e455f7d3069062957d4363879836ce. Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → WithTop ℝ≥0) :
    ∀ ω t, ContinuousWithinAt
      (fun u : ℝ≥0 =>
        MeasureTheory.stoppedProcess
          (fun s ω => x + X.X s ω - rightLimit D s ω) τ u ω)
      (Set.Ici t) t := by
  intro ω t
  have hPre (r : ℝ≥0) :
      ContinuousWithinAt
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (Ici r) r := by
    exact (continuousWithinAt_const.add (X.rightCont ω r)).sub
      (dividendStrategy_rightLimit_rightContinuous D hD ω r)
  by_cases hTop : τ ω = ⊤
  · have heq :
        (fun u : ℝ≥0 =>
          MeasureTheory.stoppedProcess
            (fun s ω => x + X.X s ω - rightLimit D s ω) τ u ω) =
        (fun u => x + X.X u ω - rightLimit D u ω) := by
      funext u
      rw [MeasureTheory.stoppedProcess_eq_of_le]
      simp only [hTop, le_top]
    rw [heq]
    exact hPre t
  · lift τ ω to ℝ≥0 using hTop with s hs
    have heq :
        (fun u : ℝ≥0 =>
          MeasureTheory.stoppedProcess
            (fun v ω => x + X.X v ω - rightLimit D v ω) τ u ω) =
        (fun u => x + X.X (min u s) ω - rightLimit D (min u s) ω) := by
      funext u
      simp only [MeasureTheory.stoppedProcess]
      rw [← hs, ← WithTop.coe_min,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [heq]
    apply (hPre (min t s)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (ContinuousAt.continuousWithinAt
        (continuousAt_id.min (continuousAt_const :
          ContinuousAt (fun _ : ℝ≥0 => s) t))).tendsto
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact min_le_min_right s hu

