-- Prove2me | solution 1 for Formalism.L2.DIV.CoF.val_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:17:55.802898+00:00
-- url     : https://prove2.me/submissions/3464faf0-623a-4ace-b2c4-5ea6f7785bc8

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
theorem _root_.solution [Normal ℚ LL] (x : CoF ι LL) : val ι LL (star x) = conjQb ι (val ι LL x) := cLL_coe ι LL x
end Formalism.L2.DIV.CoF
