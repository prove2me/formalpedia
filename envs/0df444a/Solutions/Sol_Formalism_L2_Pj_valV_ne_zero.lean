-- Prove2me | solution 1 for Formalism.L2.Pj.valV_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:53.203977+00:00
-- url     : https://prove2.me/submissions/88f7d033-3901-4fef-8f41-0ba845547b82

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
variable (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
variable {V}
namespace Formalism.L2.Pj
theorem _root_.solution {x : K'} (hx : x ≠ 0) : valV V x ≠ 0 := by
  simpa [valV] using hx
end Formalism.L2.Pj
