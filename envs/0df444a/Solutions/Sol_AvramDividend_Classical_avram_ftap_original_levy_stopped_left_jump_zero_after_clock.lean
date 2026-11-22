-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_levy_stopped_left_jump_zero_after_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:48:39.502637+00:00
-- url     : https://prove2.me/submissions/f74df2cf-2bfa-48c3-b176-98fc037f4ea2

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adapted from FTAPTheorem42/Foundations/Paths.lean:
processLeftJump_stoppedProcess_eq_zero_of_lt.
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
    (ht : τ ω < (t : WithTop ℝ≥0)) :
    MeasureTheory.stoppedProcess X.X τ t ω -
      Function.leftLim
        (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) t =
      0 := by
  have hτTop : τ ω ≠ ⊤ := ne_top_of_lt ht
  lift τ ω to ℝ≥0 using hτTop with r hr
  have hrt : r < t := WithTop.coe_lt_coe.mp ht
  letI : NeBot (𝓝[<] t) :=
    nhdsLT_neBot_of_exists_lt ⟨r, hrt⟩
  have hValue : MeasureTheory.stoppedProcess X.X τ t ω = X.X r ω := by
    rw [MeasureTheory.stoppedProcess_eq_of_ge]
    · rw [← hr, WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe]
    · rw [← hr]
      exact WithTop.coe_le_coe.mpr hrt.le
  have hEq :
      (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) =ᶠ[𝓝[<] t]
        (fun _ => X.X r ω) := by
    filter_upwards [Ico_mem_nhdsLT hrt] with s hs
    rw [MeasureTheory.stoppedProcess_eq_of_ge]
    · rw [← hr, WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe]
    · rw [← hr]
      exact WithTop.coe_le_coe.mpr hs.1
  have hLim :
      Tendsto
        (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω)
        (𝓝[<] t) (𝓝 (X.X r ω)) :=
    tendsto_const_nhds.congr' hEq.symm
  rw [hValue, leftLim_eq_of_tendsto hLim, sub_self]

