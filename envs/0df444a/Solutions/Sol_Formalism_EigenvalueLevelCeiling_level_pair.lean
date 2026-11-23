-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.level_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:19.242939+00:00
-- url     : https://prove2.me/submissions/48609b6b-58c6-4565-8aba-b20b8c067a16

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.EigenvalueLevelCeiling
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : LevelPair := by
  unfold LevelPair
  intro en enc T vs vsc nn nnc frn Dp Dm F h1 h2 hT hf hvs hvsc hn hF
  subst hvs hvsc hF
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩
end Formalism.EigenvalueLevelCeiling
