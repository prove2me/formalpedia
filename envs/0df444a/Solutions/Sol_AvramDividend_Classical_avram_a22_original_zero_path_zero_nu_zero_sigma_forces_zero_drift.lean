-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_zero_path_zero_nu_zero_sigma_forces_zero_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T20:57:22.112448+00:00
-- url     : https://prove2.me/submissions/07d51efc-05bd-4570-9f26-e42408ea37bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Laplace law of a constant zero Lévy path forces its drift to vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hNu : Y.ν = 0) (hSigma : Y.σ = 0)
    (hPath : ∀ t : ℝ≥0, ∀ ω : Ω, Y.X t ω = 0) :
    Y.c = 0 := by
  letI : IsProbabilityMeasure P := Y.isProbability
  have hLaw := (Y.laplace 1 1 (by norm_num)).2
  have hExp : Real.exp Y.c = 1 := by
    simpa [hNu, hSigma, hPath,
      laplaceExponent_zero_jump_measure] using hLaw.symm
  have hExp0 : Real.exp Y.c = Real.exp 0 := by
    simpa using hExp
  exact Real.exp_injective hExp0
