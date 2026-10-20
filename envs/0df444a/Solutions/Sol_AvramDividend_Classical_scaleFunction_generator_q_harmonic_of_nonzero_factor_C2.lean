-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T01:08:11.391159+00:00
-- url     : https://prove2.me/submissions/7f54254a-bbcc-4c16-89b7-9b86c15147ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_vcstar_contDiff_two
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Q-harmonicity of the q-scale function below the optimal barrier in the C2
branch: the jump-integrability comes from the C2 regularity of the scale
function, and the pointwise harmonicity from the continuity of the generator
residual together with its almost-everywhere vanishing. -/


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hbranch : W 0 = 0 ∨ X.BoundedVariation)
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 (cstar W).toReal)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by
  have hharm : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0 :=
    scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero
      X hX q hq W hW hc hk hvc hbranch hae
  intro x hx
  refine ⟨?_, hharm x hx⟩
  exact scaleFunction_generatorIntegrable_of_vcstar_contDiff_two
    X q W hW hvc hk x hx

