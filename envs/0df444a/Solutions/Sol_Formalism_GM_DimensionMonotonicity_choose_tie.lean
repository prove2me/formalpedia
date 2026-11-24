-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.choose_tie
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:37.856351+00:00
-- url     : https://prove2.me/submissions/18f5045e-093b-46bc-9bfc-690b4d2d5672

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
    (h : ∃ j, T.pos j + 1 = T.pos i + 1) : Classical.choose h = i := by
  have := Classical.choose_spec h
  exact hadm.1.injective (by omega)
end Formalism.GM.DimensionMonotonicity
