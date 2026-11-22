-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.mem_cls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:45:24.333797+00:00
-- url     : https://prove2.me/submissions/3c15af5c-81e4-44b0-a96e-6889a8714f3b

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {X : Type}
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution {r : Setoid X} {q : Quotient r} {y : X} :
    y ∈ cls r q ↔ Quotient.mk r y = q := Iff.rfl
end Formalism.DoubleCosetMeasures.P
