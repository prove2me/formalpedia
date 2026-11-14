-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB260_original_good_dividend_cell_reserve_hit_forces_small_gaussian_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:50:16.425829+00:00
-- url     : https://prove2.me/submissions/8a650673-511d-4a09-8ddd-0b004330d335

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t u : ℝ≥0) (hst : s ≤ t) (htu : t < u)
    (x b epsilon : ℝ)
    (hSmall : D u ω - D s ω ≤ epsilon)
    (hHit : x + X.X t ω - rightLimit D t ω = b) :
    X.X t ω - X.X s ω ∈
      Icc (b - x - X.X s ω + D s ω)
        (b - x - X.X s ω + D s ω + epsilon) := by
  have hmono : Monotone (fun v : ℝ≥0 => D v ω) := hD.2.1 ω
  have hLow : D s ω ≤ rightLimit D t ω :=
    (hmono hst).trans (dividendStrategy_le_rightLimit D hD ω t)
  have hBound : BddBelow (Set.range (fun v : Ioi t => D v.1 ω)) := by
    refine ⟨D t ω, ?_⟩
    rintro z ⟨v, rfl⟩
    exact hmono (le_of_lt v.property)
  have hHigh : rightLimit D t ω ≤ D u ω := by
    unfold rightLimit
    exact ciInf_le hBound ⟨u, htu⟩
  change (b - x - X.X s ω + D s ω ≤ X.X t ω - X.X s ω) ∧
    (X.X t ω - X.X s ω ≤ b - x - X.X s ω + D s ω + epsilon)
  constructor <;> linarith
