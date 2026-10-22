-- Prove2me | solution 1 for AvramDividend.Classical.chat07_vcstar_pure_jump_cap_harmonic_of_differentiable_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:02:41.991873+00:00
-- url     : https://prove2.me/submissions/65de4805-80d1-41aa-842c-7eccd6127c85

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_vcstar_cap_harmonic_pure_jump_of_first_fit
import Theorems.Thm_AvramDividend_Classical_vcstar_first_deriv_smooth_fit_of_nonzero
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! The pure-jump cap harmonicity follows from the established smooth fit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ)
    (hsupport : ∀ z : ℝ, z < 0 → W z = 0)
    (ha : 0 < (cstar W).toReal)
    (hWdiff : DifferentiableAt ℝ W (cstar W).toReal)
    (hWderiv : deriv W (cstar W).toReal ≠ 0)
    (hdom : X.GeneratorIntegrable W (cstar W).toReal)
    (hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z)
      (Ioc 0 (cstar W).toReal))
    (hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by
  exact chat07_vcstar_cap_harmonic_pure_jump_of_first_fit
    X hσ q W hsupport (cstar W).toReal ha rfl
    hdom hcont hinside
    (vcstar_first_deriv_smooth_fit_of_nonzero W ha hWdiff hWderiv)
