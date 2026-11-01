-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_full_hjb_from_interior_equation_and_bounded_strip_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:04:31.732708+00:00
-- url     : https://prove2.me/submissions/11810209-3e4e-4919-af79-8f473ff8139d

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_all_positive_generator_domain_of_root_smoothness
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_full_hjb_of_interior_harmonicity_and_bounded_strip_residual
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Full original-source HJB needs only scalar interior harmonicity and bounded strip sign. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hres_strip : ∀ y : ℝ,
      (cstar W).toReal < y →
      y < (cstar W).toReal + 1 + max 0 (X.c / q) →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (hinside_eq : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator (vcstar W) x - q * vcstar W x = 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  have hdomain :=
    avram_wave4_05_original_all_positive_generator_domain_of_root_smoothness
      X hX q hq W hW h_smooth
  apply avram_wave4_05_full_hjb_of_interior_harmonicity_and_bounded_strip_residual
    X hX q hq W hW h_smooth hres_strip
  intro hcpos x hx
  exact ⟨hdomain x (mem_Ioo.mp hx).1, hinside_eq hcpos x hx⟩
