-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_levy_stopped_left_jump_before_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:47:52.003977+00:00
-- url     : https://prove2.me/submissions/2f4c9ca5-bcdd-4f7d-b5f2-7564fd7eec1d

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adapted from FTAPTheorem42/Foundations/Paths.lean:
processLeftJump_stoppedProcess_eq_of_le.
Upstream commit 8c9c46e1b6e455f7d3069062957d4363879836ce.
Released under Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) ≤ τ ω) :
    MeasureTheory.stoppedProcess X.X τ t ω -
      Function.leftLim
        (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) t =
    X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by
  have hPre :
      (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) =ᶠ[𝓝[<] t]
        (fun s => X.X s ω) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    apply MeasureTheory.stoppedProcess_eq_of_le
    exact (WithTop.coe_le_coe.mpr hs.le).trans ht
  by_cases hZero : t = 0
  · subst t
    have hStoppedZero :
        Function.leftLim
          (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) 0 =
        MeasureTheory.stoppedProcess X.X τ 0 ω :=
      leftLim_eq_of_isBot isBot_bot
    have hOriginalZero :
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) 0 = X.X 0 ω :=
      leftLim_eq_of_isBot isBot_bot
    rw [hStoppedZero, hOriginalZero, MeasureTheory.stoppedProcess_eq_of_le ht]
  · have htPos : 0 < t := (pos_iff_ne_zero).mpr hZero
    obtain ⟨l, hLeft⟩ := X.leftLim ω t htPos
    letI : NeBot (𝓝[<] t) :=
      nhdsLT_neBot_of_exists_lt ⟨0, htPos⟩
    have hStopped :
        Tendsto
          (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω)
          (𝓝[<] t) (𝓝 l) :=
      hLeft.congr' hPre.symm
    calc
      MeasureTheory.stoppedProcess X.X τ t ω -
          Function.leftLim
            (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) t =
          X.X t ω - Function.leftLim
            (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) t := by
              rw [MeasureTheory.stoppedProcess_eq_of_le ht]
      _ = X.X t ω - l := by rw [leftLim_eq_of_tendsto hStopped]
      _ = X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by
            rw [leftLim_eq_of_tendsto hLeft]

