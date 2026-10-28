-- Prove2me | solution 1 for AvramDividend.Classical.killed_survival_capital_antitone_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:13:09.102018+00:00
-- url     : https://prove2.me/submissions/e9ab4efb-e328-40c2-9fd3-b0cc00cd04bd

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_killed_survival_joint_tonelli

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Killed-survival capital Laplace mass decreases with the observation horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t u : ℝ≥0) (htu : t ≤ u) (θ : ℝ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ u → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) ≤
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) := by
  apply lintegral_mono
  intro x
  apply lintegral_mono
  intro ω
  change
    Set.indicator
      {p : ℝ × Ω | 0 < p.1 ∧
        ∀ s : ℝ≥0, s ≤ u → 0 ≤ p.1 + X.X s p.2}
      (fun p => ENNReal.ofReal (Real.exp (-θ * p.1))) (x, ω) ≤
    Set.indicator
      {p : ℝ × Ω | 0 < p.1 ∧
        ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
      (fun p => ENNReal.ofReal (Real.exp (-θ * p.1))) (x, ω)
  by_cases hu : 0 < x ∧
      ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω
  · have hU : (x, ω) ∈ {p : ℝ × Ω | 0 < p.1 ∧
        ∀ s : ℝ≥0, s ≤ u → 0 ≤ p.1 + X.X s p.2} := hu
    have hT : (x, ω) ∈ {p : ℝ × Ω | 0 < p.1 ∧
        ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2} :=
      ⟨hu.1, fun s hs => hu.2 s (hs.trans htu)⟩
    simp only [Set.indicator_of_mem hU, Set.indicator_of_mem hT]
    exact le_rfl
  · have hU : (x, ω) ∉ {p : ℝ × Ω | 0 < p.1 ∧
        ∀ s : ℝ≥0, s ≤ u → 0 ≤ p.1 + X.X s p.2} := hu
    rw [Set.indicator_of_notMem hU]
    exact zero_le
