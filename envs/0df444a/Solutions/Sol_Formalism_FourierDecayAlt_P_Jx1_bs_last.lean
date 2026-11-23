-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.bs_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:13.814814+00:00
-- url     : https://prove2.me/submissions/3a97276f-af7c-45c1-9f27-80105f6e7300

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
theorem _root_.solution (h : TB.Pt E) (s : ℕ) (t : E) :
    TB.blockStart (h ++ [(s, t)]) h.length = TB.level h + 1 := by
  first
  | (simp [TB.blockStart, TB.level]; done)
  | (simp [TB.blockStart, TB.level, List.take_left']; done)
  | simp [TB.blockStart, TB.level, List.take_append_eq_append_take]
end Formalism.FourierDecayAlt.P.Jx1
