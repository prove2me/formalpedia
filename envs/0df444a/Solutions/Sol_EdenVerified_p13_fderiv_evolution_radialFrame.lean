-- Prove2me | solution 1 for EdenVerified.p13_fderiv_evolution_radialFrame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:23:30.074846+00:00
-- url     : https://prove2.me/submissions/427a21f1-6f3a-4164-9a14-0b36f6dabf7e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_fderiv_evolution_radialFrame


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace),
    fderiv ℝ (evolution c t) p (radialFrame p v) =
      angularRotation t (radialFrame p (diagonalLinear (derivativeFactors c t p) v)) :=
  @Eden.fderiv_evolution_radialFrame
end EdenVerified
