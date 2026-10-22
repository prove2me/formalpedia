-- Prove2me | solution 1 for BirkhoffGlobalSection.partial_derivative_eq_update_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:31:20.774053+00:00
-- url     : https://prove2.me/submissions/e5b982bc-13a9-41f4-8ff3-06ed6e6b8d98

import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp
import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (F : Phase → ℝ) (s : Phase) (i : Fin 4)
    (hdiff : DifferentiableAt ℝ F s) :
    partialDerivative F s i =
      deriv (fun t : ℝ => F (Function.update s i t)) (s i) := by
  have hvec : Pi.single i (1 : ℝ) = coordinateVector i := by
    ext j
    by_cases h : j = i
    · subst j
      simp [Pi.single, coordinateVector]
    · simp [Pi.single, coordinateVector, h, Ne.symm h]
  have hcoord : HasDerivAt (Function.update s i) (coordinateVector i) (s i) := by
    simpa only [hvec] using hasDerivAt_update s i (s i)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (s i) hcoord (by
    ext j
    by_cases h : j = i
    · subst j
      simp [Function.update_apply]
    · simp [Function.update_apply, h, Ne.symm h])
  change HasDerivAt (fun t : ℝ => F (Function.update s i t))
    (fderiv ℝ F s (coordinateVector i)) (s i) at hcomp
  exact hcomp.deriv.symm
