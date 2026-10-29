-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_gaussian_cstar_hjb_of_interior_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:02:12.665678+00:00
-- url     : https://prove2.me/submissions/9204cff6-cefe-4c9d-97eb-404a1ddef8c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_zero_origin_C2
import Theorems.Thm_AvramDividend_Classical_chat07_vcstar_cap_harmonic_of_continuity_and_matched_jets
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_weighted_boundary_jet
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_at_positive_cstar
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal
/-- Gaussian cap HJB reduced to the genuine interior q-harmonic scale identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (ha : 0 < (cstar W).toReal)
    (hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 ∧
      max (X.generator (vcstar W) (cstar W).toReal -
          q * vcstar W (cstar W).toReal)
          (1 - deriv (vcstar W) (cstar W).toReal) = 0 := by
  let a : ℝ := (cstar W).toReal
  have hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
  have hzero : W 0 = 0 :=
    scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
      X q (le_of_lt hq) W hW
      (gaussian_psi_superlinear_of_positive_sigma X hσ)
  have hC2local : ContDiffOn ℝ 2 W (Ioo 0 (a + 1)) :=
    hC2.mono (by intro z hz; exact hz.1)
  have hdom : X.GeneratorIntegrable W a :=
    scaleFunction_generatorIntegrable_of_contDiff_two
      X q W hW (a + 1) a (by
        constructor
        · exact ha
        · linarith) hC2local
  have hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z) (Ioc 0 a) :=
    (generator_residual_continuousOn_Ioi_of_zero_origin_C2
      X q W hW hzero hC2).mono (by intro z hz; exact hz.1)
  have hjet := avram_ws01e_bf_new_gaussian_weighted_boundary_jet
    X hX q hq W hW hσ ha
  have hsecond : iteratedDeriv 2 (vcstar W) a =
      iteratedDeriv 2 (fun z : ℝ =>
        divE (W z) (scaleDeriv W a)) a := by
    exact mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hσ)) hjet.2.2
  have hcap : X.GeneratorIntegrable (vcstar W) a ∧
      X.generator (vcstar W) a - q * vcstar W a = 0 :=
    chat07_vcstar_cap_harmonic_of_continuity_and_matched_jets
      X q W hW.1 a ha rfl hdom hcont hinside hjet.2.1 hsecond
  have hfinite : cstar W < ⊤ :=
    avram_ws01e_bf_new_gaussian_cstar_lt_top X hX q hq W hW hσ
  have hpositive : (0 : ENNReal) < cstar W := by
    by_contra h
    have hz : cstar W = 0 := le_antisymm (le_of_not_gt h) bot_le
    have hzreal : a = 0 := by simp [a, hz]
    linarith
  have hunit : deriv (vcstar W) a = 1 :=
    vcstar_deriv_eq_one_at_positive_cstar
      X hX q hq W hW hfinite hpositive (Or.inl hσ)
  change X.GeneratorIntegrable (vcstar W) a ∧
    X.generator (vcstar W) a - q * vcstar W a = 0 ∧
    max (X.generator (vcstar W) a - q * vcstar W a)
      (1 - deriv (vcstar W) a) = 0
  refine ⟨hcap.1, hcap.2, ?_⟩
  rw [hcap.2, hunit] <;> norm_num
