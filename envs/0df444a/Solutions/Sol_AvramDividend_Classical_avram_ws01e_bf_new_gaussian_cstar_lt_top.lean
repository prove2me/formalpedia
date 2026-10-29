-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_gaussian_cstar_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:02:18.829992+00:00
-- url     : https://prove2.me/submissions/fdbd8b9f-3eb0-4e6a-9d77-e2cdc889a2b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_gaussian
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_gaussian_tilt_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Gaussian standing scale functions have a finite derivative-minimising barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hgauss : 0 < X.σ) :
    cstar W < ⊤ := by
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hgauss
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  obtain ⟨_, φ, hφ, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  exact cstar_finite_of_gaussian_tilt_monotone
    X q W hW hgauss φ hφ htilt hdiff
    (scaleDeriv_continuous_of_gaussian X hgauss q hq W hW)
