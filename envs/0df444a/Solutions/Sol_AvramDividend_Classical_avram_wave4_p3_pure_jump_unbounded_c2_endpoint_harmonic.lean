-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_pure_jump_unbounded_c2_endpoint_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:29:16.461338+00:00
-- url     : https://prove2.me/submissions/6680a9d4-1ecc-404b-a19d-ce1a4d7b2fb6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_standing_nonzero_scale_normaliser
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_vcstar_nonzero
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
import Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_interior_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ0 : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hinner : ContDiffOn ℝ 2 (vcstar W)
      (Ioo 0 (cstar W).toReal) :=
    hC2.mono (by intro z hz; exact hz.1)
  have hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 :=
    avram_wave4_05_standing_nonzero_scale_normaliser X hX q hq W hW hcpos
  have hWc2 :=
    scaleFunction_contDiffOn_two_of_vcstar_nonzero W hinner hk
  have hscale :=
    avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
      X hX hσ0 hnbv q hq W hW (cstar W).toReal ha hWc2
  have hinside :=
    vcstar_interior_harmonicity_of_scale_harmonicity X q W hW ha hscale
  exact avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_interior_eq
    X hX q hq W hW hc hcpos (Or.inr (Or.inr hC2))
      (fun x hx => (hinside x hx).2)
