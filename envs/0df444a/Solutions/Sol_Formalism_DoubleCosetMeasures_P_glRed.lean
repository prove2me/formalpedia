-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.glRed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:30.168558+00:00
-- url     : https://prove2.me/submissions/3cfa8680-451c-4495-bf05-5fd619e7d659

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_card_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Set Pointwise
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.GLRed := by
  intro F _ O ϖ hϖ hϖ0 hloc _ a
  exact GLRed.card_eq O a ϖ hϖ hϖ0 hloc
end Formalism.DoubleCosetMeasures.P
