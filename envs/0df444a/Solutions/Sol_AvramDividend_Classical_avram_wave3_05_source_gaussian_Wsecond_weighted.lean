-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_source_gaussian_Wsecond_weighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:53:00.981218+00:00
-- url     : https://prove2.me/submissions/923e15d3-7fbc-4374-8099-7ff281153cb1

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_Wsecond_signed
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_second_deriv_weighted_from_signed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original Gaussian q-scale has a weighted L1 second derivative for every sufficiently large admissible discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      IntegrableOn
        (fun x : ℝ => Real.exp (-(θ * x)) * deriv (deriv W) x)
        (Ioi (0 : ℝ)) volume := by
  obtain ⟨a, w, S, ha, hSL1, hsecond⟩ :=
    avram_wave3_05_source_gaussian_Wsecond_signed
      X q hq W hW hσ φ hφ hroot
  refine ⟨φ + w, ?_⟩
  intro θ hθ hθ0 hqθ
  have hWweighted : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W x)
      (Ioi (0 : ℝ)) volume := by
    simpa only [add_zero] using
      (scaleFunction_shiftedLaplace_integrable
        X q W hW θ 0 hθ0 hqθ (le_refl (0 : ℝ)))
  have hWderweighted := chat07_scale_weighted_deriv_integrable_positive_halfline
    X q W hW θ hθ0 hqθ
  exact avram_wave3_05_second_deriv_weighted_from_signed
    W S φ w θ a hθ hWweighted hWderweighted hSL1 hsecond
