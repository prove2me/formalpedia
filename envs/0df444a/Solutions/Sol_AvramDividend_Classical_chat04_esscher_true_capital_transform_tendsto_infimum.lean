-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_true_capital_transform_tendsto_infimum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:39:37.140241+00:00
-- url     : https://prove2.me/submissions/5a8bbd1e-e6f8-4c6d-be69-9d172e1bd104

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_true_capital_transform_antitone
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ β : ℝ) (hθ : 0 ≤ θ) (hβ : 0 < β) :
    Tendsto
      (fun t : ℝ≥0 => (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-β * x) *
              Real.exp (θ * X.X t ω -
                (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P
      ∂volume))
      atTop
      (nhds (⨅ t : ℝ≥0, (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-β * x) *
              Real.exp (θ * X.X t ω -
                (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P
      ∂volume))) := by
  let F : ℝ≥0 → ℝ≥0∞ := fun t =>
    (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-β * x) *
              Real.exp (θ * X.X t ω -
                (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P
      ∂volume)
  have hAnti : Antitone F := by
    intro t u htu
    exact chat04_esscher_true_capital_transform_antitone
      X θ β hθ hβ t u htu
  have hBelow : BddBelow (Set.range F) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, rfl⟩
    exact bot_le
  exact tendsto_atTop_ciInf hAnti hBelow
