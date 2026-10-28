-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_capped_firstClosedHit_posthit_negative_of_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:01:13.279613+00:00
-- url     : https://prove2.me/submissions/21ba342c-3000-4687-97f8-19b7fc31bed8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.Order.Interval.Set.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_closedLevelHit_stoppingTime
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_negative_near_zero_of_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (x : ℝ)
    (times horizons : ℕ → ℝ≥0)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) + s) ω -
        X.X (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω < 0 := by
  let τ : Ω → ℝ≥0 := fun ω =>
    sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})
  have hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) := by
    exact reflectedSup_capped_closedLevelHit_stoppingTime X H x
  have hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s} := by
    intro s
    simpa only [WithTop.coe_le_coe] using hstop s
  exact levy_finiteStopping_negative_near_zero_of_grid
    X τ hτ hstop times horizons hcofinal hGridAE
