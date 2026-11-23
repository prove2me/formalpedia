-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.suppJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:48.119867+00:00
-- url     : https://prove2.me/submissions/34c49b5f-fc21-4f03-8450-1873cf8cf49d

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Theorems.Thm_P2M_Formalism_DoubleCosetMeasures_P_LemmaU_suppJ__bdf06674c24b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ComplexConjugate
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.SuppJ := Formalism.DoubleCosetMeasures.P.LemmaU.suppJ'
end Formalism.DoubleCosetMeasures.P
