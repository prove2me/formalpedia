-- Prove2me | solution 1 for BirkhoffGlobalSection.scaled_hamiltonian_variation_pairing_conserved
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:50.323962+00:00
-- url     : https://prove2.me/submissions/4de0498d-c252-4fb7-b597-c925fba222a4

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F b : Phase → ℝ) (q v w : ℝ → Phase)
    (hF : ∀ t, ContDiffAt ℝ ∞ F (q t))
    (hb : ∀ t, DifferentiableAt ℝ b (q t))
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) (q t) (v t)) t)
    (hw : ∀ t, HasDerivAt w
      (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) (q t) (w t)) t)
    (hvE : ∀ t, fderiv ℝ F (q t) (v t) = 0)
    (hwE : ∀ t, fderiv ℝ F (q t) (w t) = 0),
    ∀ t, phaseSymplecticForm (v t) (w t) = phaseSymplecticForm (v 0) (w 0) := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.1
