-- Prove2me | solution 1 for Formalism.L2.Col.LocOp.op_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:07.249214+00:00
-- url     : https://prove2.me/submissions/24811e0a-13a7-445d-9011-1db61c1913d9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq

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
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
attribute [instance] GSD.grpG GSD.actD GSD.addV GSD.modV GSD.modOV GSD.towV GSD.finιV GSD.decιV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.LocOp
variable {S S' : GSD K} (A : LocOp S S')
namespace Formalism.L2.Col.LocOp
theorem _root_.solution (φ : S.EqFun) (d' : S'.D) :
    ((A.op φ : S'.EqFun) : S'.D → S'.V) d' = (A.ker d').sum fun d k => k ((φ : S.D → S.V) d) := rfl
end Formalism.L2.Col.LocOp
