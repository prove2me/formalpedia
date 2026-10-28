-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_payoff_monotone_initial_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:55:19.951034+00:00
-- url     : https://prove2.me/submissions/0a5083ba-9057-4045-a131-81e4340e4e05

import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The whole-history killed scale payoff is monotone in initial capital. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x y : ℝ) (hxy : x ≤ y) (t : ℝ≥0) (ω : Ω) :
    ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
      (fun u => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ≤
    ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s u}).indicator
      (fun u => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (y + X.X t u))) ω := by
  classical
  let Sx : Set Ω := {u | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}
  let Sy : Set Ω := {u | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s u}
  have hsubset : Sx ⊆ Sy := by
    intro u hu s hs
    exact le_trans (hu s hs) (add_le_add_left hxy (X.X s u))
  change Sx.indicator (fun u => ENNReal.ofReal
    (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ≤
    Sy.indicator (fun u => ENNReal.ofReal
      (Real.exp (-(q * (t : ℝ))) * W (y + X.X t u))) ω
  by_cases hω : ω ∈ Sx
  · have hωy : ω ∈ Sy := hsubset hω
    simp only [Set.indicator_of_mem hω, Set.indicator_of_mem hωy]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left
    · exact (scaleFunction_monotone X q W hW)
        (add_le_add_left hxy (X.X t ω))
    · exact Real.exp_nonneg _
  · simp only [Set.indicator_of_notMem hω]
    exact bot_le
