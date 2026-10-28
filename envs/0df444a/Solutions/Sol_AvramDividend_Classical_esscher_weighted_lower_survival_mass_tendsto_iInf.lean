-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_lower_survival_mass_tendsto_iInf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:20:43.214986+00:00
-- url     : https://prove2.me/submissions/073dacaf-93dc-4790-95be-978eef9aad66

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_antitone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal
open AvramDividend.Classical

/--
The Esscher-weighted mass of paths surviving above a shifted lower
barrier converges, as the deterministic horizon diverges, to its
infimum over all finite horizons.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    Tendsto
      (fun t : ℝ≥0 =>
        ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
      atTop
      (nhds (⨅ t : ℝ≥0,
        ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) := by
  let mass : ℝ≥0 → ℝ := fun t =>
    ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp
        (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P
  have hAnti : Antitone mass := by
    intro t u htu
    exact esscher_weighted_lower_survival_mass_antitone X θ hθ x t u htu
  have hNonneg : ∀ t : ℝ≥0, 0 ≤ mass t := by
    intro t
    change 0 ≤ ∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P
    apply integral_nonneg
    intro ω
    by_cases hω : ω ∈ {ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}
    · rw [Set.indicator_of_mem hω]
      exact le_of_lt (Real.exp_pos _)
    · simp [Set.indicator_apply, hω]
  have hBelow : BddBelow (Set.range mass) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, rfl⟩
    exact hNonneg t
  exact tendsto_atTop_ciInf hAnti hBelow
