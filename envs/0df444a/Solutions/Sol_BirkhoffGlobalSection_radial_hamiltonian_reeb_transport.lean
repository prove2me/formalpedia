-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_hamiltonian_reeb_transport
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:12:08.405443+00:00
-- url     : https://prove2.me/submissions/d3f5d253-5f22-4a3e-b218-5b556d2e82e0

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (a F : Phase → ℝ) (u T : Phase)
    (ha : DifferentiableAt ℝ a u)
    (ht : u 0 * T 0 + u 1 * T 1 + u 2 * T 2 + u 3 * T 3 = 0)
    (hpush : fderiv ℝ (fun x : Phase => a x • x) u T =
      hamiltonianVectorField F (a u • u))
    (hlevel : ∀ w : Phase,
      u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ F (a u • u)
        (fderiv ℝ (fun x : Phase => a x • x) u w) = 0)
    (hpos : 0 < phaseRadialContact (a u • u)
      (hamiltonianVectorField F (a u • u))),
    let c := phaseRadialContact (a u • u) (hamiltonianVectorField F (a u • u))
    let R := c⁻¹ • T
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
      (a u)^2 * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x R) u w = 0) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0, 0, 0}.2.1
