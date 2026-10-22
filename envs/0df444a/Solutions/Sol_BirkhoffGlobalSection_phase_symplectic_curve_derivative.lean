-- Prove2me | solution 1 for BirkhoffGlobalSection.phase_symplectic_curve_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:47.23503+00:00
-- url     : https://prove2.me/submissions/87923af2-7ff4-4242-af03-50abcc503cd1

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (v w : ℝ → Phase) (t : ℝ) (a b : Phase)
    (hv : HasDerivAt v a t) (hw : HasDerivAt w b t),
    HasDerivAt (fun s => phaseSymplecticForm (v s) (w s))
      (phaseSymplecticForm a (w t) + phaseSymplecticForm (v t) b) t := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.1
