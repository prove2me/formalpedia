-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.coeLin_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:40.554374+00:00
-- url     : https://prove2.me/submissions/22c235f6-5921-4ebf-948e-c485abf810f1

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Function.Injective (coeLin R : (Fin n → R) →ₗ[R] (Fin n → K)) := by
  intro v w h
  funext j
  have hj := congrFun h j
  rw [coeLin_apply, coeLin_apply] at hj
  exact Subtype.ext hj
end Formalism.DoubleCosetMeasures.P
