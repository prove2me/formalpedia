-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_all_cap_sharp_upper_hjb
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:33:46.458179+00:00
-- url     : https://prove2.me/submissions/88ea80b2-d1e1-4d4c-8a8b-b3118191e62e

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_continuousOn_Icc_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_left_affine_majorant_of_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_affine_majorant_at_threshold
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_linear_residual_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For zero or positive caps, combine the gradient-controlled near-field
estimate with the true compensated affine generator bound at zero cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  by_cases hpos : 0 < (cstar W).toReal
  · have hcont :
        ContinuousOn (vcstar W) (Icc 0 (cstar W).toReal) :=
      vcstar_continuousOn_Icc_below_positive_cstar X q W hW hpos
    have hdiff : ∀ z ∈ Ioo (0 : ℝ) (cstar W).toReal,
        DifferentiableAt ℝ (vcstar W) z := by
      intro z hz
      exact (vcstar_deriv_ge_one X hX q hq W hW z hz.1).1
    have hder : ∀ z ∈ Ioo (0 : ℝ) (cstar W).toReal,
        1 ≤ deriv (vcstar W) z := by
      intro z hz
      exact (vcstar_deriv_ge_one X hX q hq W hW z hz.1).2
    have hchord :=
      left_affine_majorant_of_deriv_ge_one
        (vcstar W) (cstar W).toReal (le_of_lt hpos) hcont hdiff hder
    exact vcstar_near_HJB_of_affine_majorant_at_threshold
      X q hq W hW hpos hchord x hx hx1 hthreshold
  have hanonneg : 0 ≤ (cstar W).toReal :=
    ENNReal.toReal_nonneg
  have hazero : (cstar W).toReal = 0 :=
    le_antisymm (le_of_not_gt hpos) hanonneg
  have hfar : (cstar W).toReal + 1 ≤ x := by
    rw [hazero]
    linarith
  obtain ⟨hdom, _, hres⟩ :=
    avram_wave4_05_source_far_field_generator_linear_residual_bound
      X hX q hq W hW x hfar
  have hdiv : X.c / q ≤ x - (cstar W).toReal := by
    have hmax : X.c / q ≤ max (0 : ℝ) (X.c / q) :=
      le_max_right 0 (X.c / q)
    linarith
  have hmul : X.c ≤ (x - (cstar W).toReal) * q :=
    (div_le_iff₀ hq).mp hdiv
  have hnonpos :
      X.generator (vcstar W) x - q * vcstar W x ≤ 0 := by
    nlinarith
  refine ⟨hdom, ?_⟩
  have hder := vcstar_deriv_eq_one_above_cstar W x hx
  simpa [hder] using (max_eq_right hnonpos)
