-- Prove2me | solution 1 for FirstPassageLinearTransport.pure_multiplicative_le_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:21:46.365748+00:00
-- url     : https://prove2.me/submissions/f0792f72-1883-4c3a-8827-1b9b37472b90

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_exact_affine_iterate_real


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n j : ℕ) :
    ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) ≤
      (orbit j n : ℝ) := by
  rw [exact_affine_iterate_real]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _hi => by positivity)
end FirstPassageLinearTransport
