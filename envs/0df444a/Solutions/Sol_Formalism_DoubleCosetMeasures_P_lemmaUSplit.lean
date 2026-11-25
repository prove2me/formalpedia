-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.lemmaUSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:58:43.829565+00:00
-- url     : https://prove2.me/submissions/a27b79d6-cee5-4a24-8393-54c2828e7c78

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_LemmaU_lemmaU

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
theorem _root_.solution : Formalism.DoubleCosetMeasures.LemmaUSplit := Formalism.DoubleCosetMeasures.P.LemmaU.lemmaU
end Formalism.DoubleCosetMeasures.P
