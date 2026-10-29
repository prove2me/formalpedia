-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_gaussian_weighted_boundary_jet
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:50:29.914808+00:00
-- url     : https://prove2.me/submissions/b4bfa0e2-3c3f-4b09-9770-1d9e68131406

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous
import Theorems.Thm_AvramDividend_Classical_vcstar_first_deriv_smooth_fit_of_nonzero
import Theorems.Thm_AvramDividend_Classical_vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_cstar_lt_top
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (ha : 0 < (cstar W).toReal) :
    (∀ z : ℝ, z ≤ (cstar W).toReal →
      vcstar W z = (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) z) ∧
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
    X.σ ^ 2 * iteratedDeriv 2 (vcstar W) (cstar W).toReal =
      X.σ ^ 2 * iteratedDeriv 2 (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal := by
  have hC2 := scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
  have hWdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y := fun y hy =>
    (hC2.differentiableOn (by norm_num) y (Set.mem_Ioi.2 hy)).differentiableAt (Ioi_mem_nhds hy)
  obtain ⟨hWpos, φ, hφ, hmono⟩ := scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hlow := normalized_derivative_lower_bound φ _ hmono ha (hWdiff _ ha)
  have hWderiv : deriv W (cstar W).toReal ≠ 0 :=
    (lt_of_lt_of_le (mul_pos hφ (hWpos _ ha)) hlow).ne'
  have hD1 : ContDiffOn ℝ 1 (deriv W) (Set.Ioi 0) :=
    hC2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdd : DifferentiableAt ℝ (deriv W) (cstar W).toReal :=
    (hD1.differentiableOn one_ne_zero _ (Set.mem_Ioi.2 ha)).differentiableAt (Ioi_mem_nhds ha)
  have hzero := AvramDividend.Classical.deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous W
    hD1.continuousOn ha
  have hWstat : HasDerivAt (deriv W) 0 (cstar W).toReal := by
    have := hdd.hasDerivAt; rwa [hzero] at this
  have hc := AvramDividend.Classical.avram_ws01e_bf_new_gaussian_cstar_lt_top X hX q hq W hW hσ
  have hcpos : 0 < cstar W := (ENNReal.toReal_pos_iff.1 ha).1
  have hv1 := vcstar_deriv_eq_one_at_positive_cstar X hX q hq W hW hc hcpos (Or.inl hσ)
  have h2 := vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv W ha hWdiff hWderiv hWstat hv1
  refine ⟨fun z hz => AvramDividend.Classical.vcstar_eq_scaledW_le_cstar_of_support W hW.1 z hz,
    vcstar_first_deriv_smooth_fit_of_nonzero W ha (hWdiff _ ha) hWderiv, ?_⟩
  simp only [iteratedDeriv_eq_iterate, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    Function.id_def]
  rw [h2]
