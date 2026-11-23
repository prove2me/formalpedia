-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.level_append
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:39.887446+00:00
-- url     : https://prove2.me/submissions/60e66d25-d9f5-437c-9b42-e9346f03d3af

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
variable {E : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution (h : TB.Pt E) (s : ℕ) (t : E) : TB.level (h ++ [(s, t)]) = TB.level h + s := by
  simp [TB.level]
end Formalism.FourierDecayAlt.P.Jx1
