-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.bs_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:55.258984+00:00
-- url     : https://prove2.me/submissions/59405956-c0c1-4e8b-92c5-15a3442e961c

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
theorem _root_.solution (h : TB.Pt E) (s : ℕ) (t : E) (k : ℕ) (hk : k < h.length) :
    TB.blockStart (h ++ [(s, t)]) k = TB.blockStart h k := by
  first
  | (simp only [TB.blockStart, List.take_append_of_le_length hk.le]; done)
  | (simp [TB.blockStart, List.take_append, hk.le]; done)
  | simp [TB.blockStart, List.take_append_eq_append_take, Nat.sub_eq_zero_of_le hk.le]
end Formalism.FourierDecayAlt.P.Jx1
