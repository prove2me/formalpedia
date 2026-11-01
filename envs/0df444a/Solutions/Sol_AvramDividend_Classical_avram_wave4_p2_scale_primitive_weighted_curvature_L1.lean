-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_weighted_curvature_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:06:38.332908+00:00
-- url     : https://prove2.me/submissions/63869494-619f-481e-8a17-4c1e8755231c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Genuine source weighted primitive curvature is a global measurable L1 function. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    Measurable ((Ioi (0 : ℝ)).indicator (deriv W)) ∧
      ContinuousOn ((Ioi (0 : ℝ)).indicator (deriv W)) (Ioi (0 : ℝ)) ∧
      Integrable
        (fun u : ℝ => Real.exp (-(θ * u)) *
          |(Ioi (0 : ℝ)).indicator (deriv W) u|) volume := by
  let F : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (deriv W)
  have hDmeas : Measurable (deriv W) := measurable_deriv W
  have hFm : Measurable F :=
    hDmeas.indicator measurableSet_Ioi
  have hWcd : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hDcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) :=
    hWcd.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl 1)
  have hFc : ContinuousOn F (Ioi (0 : ℝ)) := by
    apply hDcont.congr
    intro x hx
    simp only [F, indicator_of_mem hx]
  have hWI :=
    chat07_scale_weighted_deriv_integrable_positive_halfline
      X q W hW θ hθ hqθ
  have hIabs : IntegrableOn
      (fun u : ℝ => Real.exp (-(θ * u)) * |deriv W u|)
      (Ioi (0 : ℝ)) := by
    have hI0 : IntegrableOn
        (fun u : ℝ => |Real.exp (-(θ * u)) * deriv W u|)
        (Ioi (0 : ℝ)) := by
      exact hWI.abs
    have hfun :
        (fun u : ℝ => Real.exp (-(θ * u)) * |deriv W u|) =
        (fun u : ℝ => |Real.exp (-(θ * u)) * deriv W u|) := by
      funext u
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    rw [hfun]
    exact hI0
  have hEI : Integrable
      ((Ioi (0 : ℝ)).indicator
        (fun u : ℝ => Real.exp (-(θ * u)) * |deriv W u|)) volume :=
    hIabs.integrable_indicator measurableSet_Ioi
  have hEq :
      (fun u : ℝ => Real.exp (-(θ * u)) * |F u|) =
      (Ioi (0 : ℝ)).indicator
        (fun u : ℝ => Real.exp (-(θ * u)) * |deriv W u|) := by
    funext u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · simp [F, indicator_of_mem hu]
    · simp [F, Set.indicator, hu]
  exact ⟨hFm, hFc, by rw [hEq]; exact hEI⟩
