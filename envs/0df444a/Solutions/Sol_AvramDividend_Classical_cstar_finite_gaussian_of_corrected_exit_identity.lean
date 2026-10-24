-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_gaussian_of_corrected_exit_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:02:18.52873+00:00
-- url     : https://prove2.me/submissions/7c0bfb50-a4d3-40a5-b2ac-fb2b4557f967

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_gaussian_tilt_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Finite Gaussian optimal barrier from corrected killed-exit identity.
The Gaussian scale is C1 and the associated Esscher tilt is monotone. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    cstar W < ⊤ := by
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact hreg.differentiableOn_one.differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  have hcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) :=
    hreg.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  obtain ⟨φ, hφ, _, hmono⟩ :=
    gaussian_tilt_monotone_of_corrected_exit_identity
      X q hq W hW hσ hExit
  exact cstar_finite_of_gaussian_tilt_monotone
    X q W hW hσ φ hφ hmono hdiff hcont
