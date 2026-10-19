-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_scaledW_boundary_smooth_fit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-18T18:07:30.531487+00:00
-- url     : https://prove2.me/submissions/e8ccabfa-22d0-435b-b75e-8379aca0eacf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_cstar_positive_boundary_regularity_package
import Theorems.Thm_AvramDividend_Classical_vcstar_first_deriv_smooth_fit_of_nonzero
import Theorems.Thm_AvramDividend_Classical_vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
    X.σ ^ 2 * iteratedDeriv 2 (vcstar W) (cstar W).toReal =
      X.σ ^ 2 * iteratedDeriv 2 (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal := by
  let c : ℝ := (cstar W).toReal
  have hcr : 0 < c := by
    exact (ENNReal.toReal_pos_iff).2 ⟨hcpos, hc⟩
  obtain ⟨hWdiff, hWderivNe, hWstationary⟩ :=
    AvramDividend.Classical.scaleFunction_cstar_positive_boundary_regularity_package
      X hX q hq W hW hc hcpos
  have hne : deriv W c ≠ 0 := hWderivNe
  have hdiffC : DifferentiableAt ℝ W c := hWdiff c hcr
  have hfirst :
      deriv (vcstar W) c =
        deriv (fun z : ℝ => divE (W z) (scaleDeriv W c)) c :=
    AvramDividend.Classical.vcstar_first_deriv_smooth_fit_of_nonzero
      W hcr hdiffC hne
  constructor
  · exact hfirst
  · by_cases hσ : X.σ = 0
    · simp [hσ]
    · have hscale : scaleDeriv W c = ((deriv W c : ℝ) : EReal) := by
        simp [scaleDeriv, hcr.ne']
      have hdiv (z : ℝ) :
          divE (W z) (scaleDeriv W c) = W z / deriv W c := by
        simp [hscale, divE]
      have hfun :
          (fun z : ℝ => divE (W z) (scaleDeriv W c)) =
            (fun z : ℝ => W z / deriv W c) := funext hdiv
      have hscaledOne :
          deriv (fun z : ℝ => divE (W z) (scaleDeriv W c)) c = 1 := by
        rw [hfun]
        have hd : HasDerivAt (fun z : ℝ => W z / deriv W c) 1 c := by
          simpa [hne] using (hdiffC.hasDerivAt.div_const (deriv W c))
        exact hd.deriv
      have hfirstOne : deriv (vcstar W) c = 1 := hfirst.trans hscaledOne
      have hsecond :
          deriv (deriv (vcstar W)) c =
            deriv (deriv (fun z : ℝ =>
              divE (W z) (scaleDeriv W c))) c :=
        AvramDividend.Classical.vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
          W hcr hWdiff hne (hWstationary hσ) hfirstOne
      simpa only [show (2 : ℕ) = 1 + 1 from rfl,
        iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        congrArg (fun a : ℝ => X.σ ^ 2 * a) hsecond
