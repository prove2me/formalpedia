-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Iso.onForms_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:10:07.222561+00:00
-- url     : https://prove2.me/submissions/c5e3ea82-25fc-4873-a27a-9bba58102162

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
open Formalism.L2.Col.GSD Formalism.L2.Col.GSD.Iso
variable {S S' : GSD K} (e : GSD.Iso S S')
namespace Formalism.L2.Col.GSD.Iso
theorem _root_.solution (φ : S.EqFun) (d' : S'.D) :
    ((e.onForms φ : S'.EqFun) : S'.D → S'.V) d' = e.eV ((φ : S.D → S.V) (e.eD.symm d')) := rfl
end Formalism.L2.Col.GSD.Iso
