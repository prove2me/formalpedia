-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pds_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:27.25606+00:00
-- url     : https://prove2.me/submissions/a62e9f8e-60f7-48d1-863b-df012a665a31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Formalism Formalism.IndefR Formalism.IndefR.Tow Formalism.IndefR.Tow.OrbStPf
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
namespace Formalism.IndefR.Tow.OrbStPf
theorem _root_.solution (i : Fin N) (L : List (Fin N)) (f : (Fin N → ℝ) → H) :
    pds (i :: L) f = pd i (pds L f) := rfl
end Formalism.IndefR.Tow.OrbStPf
