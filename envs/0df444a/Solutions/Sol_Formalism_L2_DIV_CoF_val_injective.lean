-- Prove2me | solution 1 for Formalism.L2.DIV.CoF.val_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:18:49.23152+00:00
-- url     : https://prove2.me/submissions/c19fd37f-41d3-45d6-9ac7-6811b77fb758

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IotaABijective
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace

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
open Formalism.L2.DIV.CoF
variable (ι : Qb →+* ℂ) (LL : Fld)
namespace Formalism.L2.DIV.CoF
theorem _root_.solution : Function.Injective (val ι LL) := by
  intro a b hab
  exact Subtype.ext hab
end Formalism.L2.DIV.CoF
