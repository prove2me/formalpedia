-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_bv_cstar_hjb_at_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:30:53.319061+00:00
-- url     : https://prove2.me/submissions/a59fc25b-682b-4b6e-9be2-bed486bbc3eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
import Theorems.Thm_AvramDividend_Classical_bv_scale_generator_q_harmonic_all_barriers_ws01b
import Theorems.Thm_AvramDividend_Classical_chat07_vcstar_pure_jump_cap_harmonic_of_differentiable_scale
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_bv_standing
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_smoothfit_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Actual BV dividend HJB at a positive barrier, including generator integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (ha : 0 < (cstar W).toReal) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 ∧
      max (X.generator (vcstar W) (cstar W).toReal -
          q * vcstar W (cstar W).toReal)
          (1 - deriv (vcstar W) (cstar W).toReal) = 0 := by
  let a : ℝ := (cstar W).toReal
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hbv
  have hdiff : DifferentiableAt ℝ W a :=
    (hC1.differentiableOn one_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds ha)
  obtain ⟨hWpos, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  have hk : 0 < deriv W a :=
    lt_of_lt_of_le (mul_pos hφ (hWpos a ha))
      (normalized_derivative_lower_bound φ a hmono ha hdiff)
  have hdom : X.GeneratorIntegrable W a :=
    scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
      X q W hW hbv a ha hC1
  have hcontIoi : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z) (Ioi 0) :=
    generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
      X hX hbv hbv.1 q W hW hC1
  have hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z) (Ioc 0 a) :=
    hcontIoi.mono (by intro z hz; exact hz.1)
  have hinside : ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by
    intro x hx
    exact (bv_scale_generator_q_harmonic_all_barriers_ws01b
      X hX q hq W hW hbv a ha x hx).2
  have hcap : X.GeneratorIntegrable (vcstar W) a ∧
      X.generator (vcstar W) a - q * vcstar W a = 0 :=
    chat07_vcstar_pure_jump_cap_harmonic_of_differentiable_scale
      X hbv.1 q W hW.1 ha hdiff (ne_of_gt hk) hdom hcont hinside
  have hfinite : cstar W < ⊤ :=
    cstar_lt_top_of_bv_standing X hX q hq W hW hbv
  have hpositive : (0 : ENNReal) < cstar W := by
    by_contra h
    have hz : cstar W = 0 := le_antisymm (le_of_not_gt h) bot_le
    have hzreal : a = 0 := by simp [a, hz]
    linarith
  have hderiv : deriv (vcstar W) a = 1 :=
    avram_ws01e_bf_new_bv_smoothfit_of_standing
      X hX q hq W hW hfinite hpositive hbv
  change X.GeneratorIntegrable (vcstar W) a ∧
    X.generator (vcstar W) a - q * vcstar W a = 0 ∧
    max (X.generator (vcstar W) a - q * vcstar W a)
      (1 - deriv (vcstar W) a) = 0
  refine ⟨hcap.1, hcap.2, ?_⟩
  rw [hcap.2, hderiv] <;> norm_num
