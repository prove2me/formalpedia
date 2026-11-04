-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_moving_mesh_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:43:08.280678+00:00
-- url     : https://prove2.me/submissions/37045eff-9a42-42c0-a3a7-eb2dcd2097ed

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_uniform_moving_taylor_quadratic_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Moving-mesh Taylor error along the actual controlled path, strictly
before a localisation clock; the path-in-band fact is supplied externally. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (hLocal : ∀ ω (s : ℝ≥0), s < τ ω → riskProcess X x D s ω ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ ω (s t : ℝ≥0), s < τ ω → t < τ ω →
        riskProcess X x D s ω ≠ riskProcess X x D t ω →
        |w (riskProcess X x D t ω) -
          taylorWithinEval w 1
            (uIcc (riskProcess X x D s ω) (riskProcess X x D t ω))
            (riskProcess X x D s ω) (riskProcess X x D t ω)| ≤
          (K / 2) *
            (riskProcess X x D t ω - riskProcess X x D s ω) ^ 2 := by
  obtain ⟨K, hK, hTaylor⟩ :=
    avram_p4_a_gaussian_ubv_C2_uniform_moving_taylor_quadratic_bound
      C w hwC2 a b hBand
  refine ⟨K, hK, ?_⟩
  intro ω s t hs ht hneq
  exact hTaylor (riskProcess X x D s ω) (hLocal ω s hs)
    (riskProcess X x D t ω) (hLocal ω t ht) hneq
