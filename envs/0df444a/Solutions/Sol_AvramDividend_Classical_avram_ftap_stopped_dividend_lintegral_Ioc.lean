-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_stopped_dividend_lintegral_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:08:00.741806+00:00
-- url     : https://prove2.me/submissions/090882e9-7160-4228-9387-306f77575a16

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adapted from FTAPTheorem42/Stochastic/FiniteVariation/FiniteVariationIntegralProcessStopping.lean
Upstream commit 8c9c46e1b6e455f7d3069062957d4363879836ce. Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ t : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioc (0 : ℝ) (t : ℝ), f s
      ∂((dividendMeasure D ω).restrict (Ioc (0 : ℝ) (τ : ℝ)))) =
    (∫⁻ s in Ioc (0 : ℝ) ((min t τ : ℝ≥0) : ℝ),
      f s ∂(dividendMeasure D ω)) := by
  have hInter :
      Ioc (0 : ℝ) (t : ℝ) ∩ Ioc (0 : ℝ) (τ : ℝ) =
        Ioc (0 : ℝ) ((min t τ : ℝ≥0) : ℝ) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioc, NNReal.coe_min, le_min_iff]
    constructor
    · rintro ⟨⟨h0, ht⟩, ⟨_, hτ⟩⟩
      exact ⟨h0, ht, hτ⟩
    · rintro ⟨h0, ht, hτ⟩
      exact ⟨⟨h0, ht⟩, ⟨h0, hτ⟩⟩
  change (∫⁻ s, f s ∂((dividendMeasure D ω).restrict
      (Ioc (0 : ℝ) (τ : ℝ))).restrict (Ioc (0 : ℝ) (t : ℝ))) = _
  rw [Measure.restrict_restrict measurableSet_Ioc, hInter]

