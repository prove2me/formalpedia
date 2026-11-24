-- Prove2me | solution 1 for Formalism.L2.Col.GSD.resOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:32:49.10185+00:00
-- url     : https://prove2.me/submissions/1f936221-ec91-4182-8fc8-bdfc7c41f6a5

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
open Formalism.L2.Col.GSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution (h : S.Ok) (s : S.Sec) (φ : S.EqFun) (c : S.Cl) :
    ((S.resOf h s φ).1 : S.Cl → S.V) c = (φ : S.D → S.V) (s.rep c) := rfl
end Formalism.L2.Col.GSD
