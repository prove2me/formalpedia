-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_killed_terminal_left_grid_lower_bound_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:59:08.528084+00:00
-- url     : https://prove2.me/submissions/99996bcd-7f52-4e21-bde2-10d7abd621bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_killed_terminal_one_sided_liminf_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Any positive-time original killed-terminal lower bound along the left filter
pulls back to an approaching natural-number grid, including exact ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (q : ℝ)
    (hwnn : ∀ ω (s : ℝ≥0), 0 < s →
      (s : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D s ω))
    (t : ℝ≥0) (ht : 0 < t) (u : ℕ → ℝ≥0)
    (hu : Tendsto u atTop (𝓝[<] t)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (if (t : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω) else 0) - ε <
        (if (u n : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (u n : ℝ))) * w (riskProcess X x D (u n) ω) else 0) := by
  filter_upwards [avram_p3_bv_original_killed_terminal_one_sided_liminf_ae
    X D hD x w hw q hwnn t ht] with ω hOneSided
  intro ε hε
  exact hu.eventually (hOneSided ε hε)
