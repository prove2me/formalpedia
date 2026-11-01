-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_vcstar_hjb_at_positive_cap_without_above_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:13:57.251848+00:00
-- url     : https://prove2.me/submissions/c187d382-2be4-47d3-aa7b-f7ca8df9d570

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      max (X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal)
        (1 - deriv (vcstar W) (cstar W).toReal) = 0 := by
  have hcap :=
    avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
      X hX q hq W hW hc hcpos h_smooth
  have hder :=
    vcstar_deriv_eq_one_at_positive_cstar
      X hX q hq W hW hc hcpos h_smooth
  refine ⟨hcap.1, ?_⟩
  rw [hcap.2, hder] <;> norm_num
