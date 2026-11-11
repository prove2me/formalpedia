-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger18_original_topcap_grid_zero_cell_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:35:48.527228+00:00
-- url     : https://prove2.me/submissions/d7e6dedb-e083-4827-a62f-23a822ab7b2f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The genuine zero grid cell lies in the same positive band as the
strictly pre-stopping positive-time cells of the original reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j n m : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
      s < ρ ω →
        riskProcess X x D s ω ∈
          Icc (min x ((1 : ℝ) / ((j : ℝ) + 1)))
            (x + ((j : ℝ) + 1)) := by
  filter_upwards [hprefix] with ω hp
  intro i hi
  dsimp
  intro hs
  by_cases hz : (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) = 0
  · have hy : riskProcess X x D 0 ω = x := by
      simp [riskProcess, X.X_zero, hD.1]
    simp only [hz, hy, mem_Icc]
    constructor
    · exact min_le_left _ _
    · have : (0 : ℝ) ≤ ((j : ℝ) + 1) := by positivity
      linarith
  · have hpositive :
        (0 : ℝ≥0) < (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) :=
      lt_of_le_of_ne bot_le (Ne.symm hz)
    obtain ⟨hlo, hhi⟩ := hp _ hpositive hs
    exact ⟨le_trans (min_le_right _ _) hlo, hhi⟩
