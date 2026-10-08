-- Prove2me | solution 1 for BookProof.ChapterDiffuseCdfModel.continuous_cdf_of_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:06:47.441465+00:00
-- url     : https://prove2.me/submissions/cc9df765-cda1-4808-85af-90bf5c8fceee

-- Generated from ChapterDiffuseCdfModel.lean — solution of BookProof.ChapterDiffuseCdfModel.continuous_cdf_of_noAtoms
import Mathlib
import Definitions.Def_ChapterDiffuseCdfModel
open BookProof.ChapterDiffuseCdfModel



noncomputable section

open MeasureTheory ProbabilityTheory Filter


variable (mu : Measure ℝ)

variable (mu : Measure ℝ)

set_option maxHeartbeats 1000000 in
theorem solution [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Continuous (cdf mu) := by

  refine continuous_iff_continuousAt.2 fun a => ?_
  have hmono : Monotone (cdf mu) := (cdf mu).mono
  have hs : (cdf mu).measure {a} = 0 := by
    rw [measure_cdf]
    simp
  have h1 : ENNReal.ofReal ((cdf mu) a - Function.leftLim (cdf mu) a) = 0 := by
    rw [← StieltjesFunction.measure_singleton]
    exact hs
  have h2 : (cdf mu) a ≤ Function.leftLim (cdf mu) a := by
    have h := (ENNReal.ofReal_eq_zero).1 h1
    linarith
  have h3 : Function.leftLim (cdf mu) a ≤ (cdf mu) a := hmono.leftLim_le le_rfl
  have hleft : Function.leftLim (cdf mu) a = (cdf mu) a := le_antisymm h3 h2
  have hright : Function.rightLim (cdf mu) a = (cdf mu) a :=
    ((cdf mu).right_continuous a).rightLim_eq
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim, hleft, hright]
