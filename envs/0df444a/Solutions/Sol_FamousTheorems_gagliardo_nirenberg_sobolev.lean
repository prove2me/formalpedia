-- Prove2me | solution 1 for FamousTheorems.gagliardo_nirenberg_sobolev
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:15:54.410097+00:00
-- url     : https://prove2.me/submissions/d00a8bb1-fe80-4d24-b3aa-ab2c9eff1259

import Mathlib

open MeasureTheory

theorem solution {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {p p' : NNReal} (hp : 1 ≤ p) (hn : 0 < Module.finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (Module.finrank ℝ E : ℝ)⁻¹) :
    ∃ C : NNReal, ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u p' μ ≤ C * eLpNorm (fderiv ℝ u) p μ :=
  ⟨_, fun _ hu h2u => MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq μ hu h2u hp hn hp'⟩
