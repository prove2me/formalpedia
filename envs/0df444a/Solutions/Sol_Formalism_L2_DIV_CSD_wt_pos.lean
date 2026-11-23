-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.wt_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:28.379772+00:00
-- url     : https://prove2.me/submissions/0a66fd0a-0898-4612-b3e7-af3aaac505e9

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution (c : S.Cl) : 0 < S.wt c := Fintype.card_pos
end Formalism.L2.DIV.CSD
