-- Prove2me | solution 1 for Formalism.L2.Col.GSD.resOf_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:18:32.327056+00:00
-- url     : https://prove2.me/submissions/e725dd0d-1517-465c-b890-887c54e1bc80

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
theorem _root_.solution (h : S.Ok) (s : S.Sec) (f : (S.toCSDOf h s).Forms) (d : S.D) :
    (((S.resOf h s).symm f : S.EqFun) : S.D → S.V) d = S.ρ (s.mv d) ((f.1 : S.Cl → S.V) (S.cls d)) := rfl
end Formalism.L2.Col.GSD
