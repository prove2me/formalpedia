-- Prove2me | solution 1 for Formalism.landauIteratedDerivatives.meas_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:03:10.60938+00:00
-- url     : https://prove2.me/submissions/dabb4613-3c07-4ac6-a22b-1b038ac8a6c9

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open Formalism.landauIteratedDerivatives
namespace Formalism.landauIteratedDerivatives
theorem _root_.solution (H : ℝ → ℝ) (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (σ : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => H x * x ^ (-σ - 1)) (volume.restrict (Ioi 1)) :=
  hH.mul (by fun_prop : Measurable fun x : ℝ => x ^ (-σ - 1)).aestronglyMeasurable
end Formalism.landauIteratedDerivatives
