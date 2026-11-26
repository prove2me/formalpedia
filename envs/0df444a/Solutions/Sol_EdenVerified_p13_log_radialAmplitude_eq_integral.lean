-- Prove2me | solution 1 for EdenVerified.p13_log_radialAmplitude_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:24:26.731972+00:00
-- url     : https://prove2.me/submissions/2f60234b-6dbc-4d6a-a73c-d2a32b0c6b05

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_log_radialAmplitude_eq_integral


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    Real.log (radialAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s) :=
  @Eden.log_radialAmplitude_eq_integral
end EdenVerified
