-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.JJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:35.592506+00:00
-- url     : https://prove2.me/submissions/e0b53e95-7f1a-49e4-a281-19386e5d9925

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : J * J = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J]
end Formalism.SLP.GlobalBoundRefinements.P
