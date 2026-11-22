-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.low_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:20:06.31956+00:00
-- url     : https://prove2.me/submissions/b8b1a06b-50fc-4329-90b5-79db853af569

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock

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
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) {i j : Fin n}
    (h : i < j) : x i j = 0 := by
  first
  | exact hx.1 h
  | exact hx.1 (show OrderDual.toDual j < OrderDual.toDual i from h)
end Formalism.DoubleCosetMeasures.P.Phase
