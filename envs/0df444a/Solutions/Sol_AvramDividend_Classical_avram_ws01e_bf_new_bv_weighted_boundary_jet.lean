-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_bv_weighted_boundary_jet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:29:14.650585+00:00
-- url     : https://prove2.me/submissions/d0bf9d04-a747-4e2e-a6af-f326538b528f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_first_deriv_smooth_fit_of_nonzero
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Bounded-variation scale and dividend branches have their full weighted boundary jet. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hc : 0 < (cstar W).toReal) :
    (∀ z : ℝ, z ≤ (cstar W).toReal →
      vcstar W z = (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) z) ∧
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
    X.σ ^ 2 * iteratedDeriv 2 (vcstar W) (cstar W).toReal =
      X.σ ^ 2 * iteratedDeriv 2 (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hbv
  have hdiff : DifferentiableAt ℝ W (cstar W).toReal :=
    (hC1.differentiableOn one_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hc)
  obtain ⟨hWpos, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  have hk : 0 < deriv W (cstar W).toReal :=
    lt_of_lt_of_le
      (mul_pos hφ (hWpos _ hc))
      (normalized_derivative_lower_bound φ _ hmono hc hdiff)
  refine ⟨vcstar_eq_scaledW_le_cstar_of_support W hW.1, ?_, ?_⟩
  · exact vcstar_first_deriv_smooth_fit_of_nonzero
      W hc hdiff (ne_of_gt hk)
  · simp [hbv.1]
