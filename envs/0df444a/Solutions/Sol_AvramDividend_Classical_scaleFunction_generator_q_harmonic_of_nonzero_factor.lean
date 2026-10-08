-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T06:16:54.304401+00:00
-- url     : https://prove2.me/submissions/2a157132-637b-4c83-b908-726dd5f5a2fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_integrable_of_nonzero_factor
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_integrable_nonzero_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by
  have hint :=
    scaleFunction_generator_integrable_of_nonzero_factor
      X hX q hq W hW h_smooth hc hk
  have hident :=
    scaleFunction_generator_eq_q_of_integrable_nonzero_factor
      X hX q hq W hW h_smooth hc hk hint
  intro x hx
  exact ⟨hint x hx, hident x hx⟩
