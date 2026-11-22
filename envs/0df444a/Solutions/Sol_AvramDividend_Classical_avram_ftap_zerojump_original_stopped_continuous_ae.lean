-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_zerojump_original_stopped_continuous_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:41:23.970825+00:00
-- url     : https://prove2.me/submissions/b5377b42-e969-4c87-8166-eeb236707497

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adapted stopped-process case split from FTAPTheorem42 Stochastic/Martingale/Basic/RightContinuousStoppedMartingale.lean.
Commit 8c9c46e1b6e455f7d3069062957d4363879836ce. Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → WithTop ℝ≥0) :
    ∀ᵐ ω ∂P, Continuous
      (fun t : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ t ω) := by
  obtain ⟨_, _, _, hContinuousX, _⟩ :=
    avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
      X hν x D hD
  filter_upwards [hContinuousX] with ω hω
  by_cases hTop : τ ω = ⊤
  · have hEq : (fun t : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ t ω) =
        fun t => X.X t ω := by
      funext t
      rw [MeasureTheory.stoppedProcess_eq_of_le]
      simp only [hTop, le_top]
    rw [hEq]
    exact hω
  · lift τ ω to ℝ≥0 using hTop with s hs
    have hEq : (fun t : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ t ω) =
        fun t => X.X (min t s) ω := by
      funext t
      simp only [MeasureTheory.stoppedProcess]
      rw [← hs, ← WithTop.coe_min,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [hEq]
    exact hω.comp (continuous_id.min continuous_const)

