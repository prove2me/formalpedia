-- Prove2me | solution 1 for Formalism.L2.DIV.isAlgebraicQb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:48.176165+00:00
-- url     : https://prove2.me/submissions/942e175c-675a-49db-ae35-8a4cb1f8ee35

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution (LL : Fld) : Algebra.IsAlgebraic LL Qb := by
  have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) LL
end Formalism.L2.DIV
